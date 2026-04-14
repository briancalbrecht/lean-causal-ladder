import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum

/-!
# Index structure is necessary (Proposition `p:index`, Appendix C)

The paper's necessity claim: if level sets of `ξ ↦ D(x, p°, ξ)` determine
level sets of `ξ ↦ D(x, p, ξ)` for every `p`, then `D` factors through the
index `δ(x, ξ) := D(x, p°, ξ)`.

**Source:** `paper/paper.tex` lines 777–797.

## Hypothesis: symmetric level-set agreement

The paper (as of commit following the Lean audit) states the hypothesis
symmetrically in the reference price (paper.tex line 778):

  > For every `x ∈ X`, every `p, p' ∈ P`, and every `ξ₁, ξ₂ ∈ Ξ`,
  > `D(x, p, ξ₁) = D(x, p, ξ₂) ⇒ D(x, p', ξ₁) = D(x, p', ξ₂)`.

This is `LevelSetsAgree` below: the level sets of `ξ ↦ D(x, p, ξ)` are the
**same** at every price. Both parts (a) and (b) follow directly.

### History: the asymmetric version was insufficient for part (b)

An earlier version of the paper (pre-2026-04-14) stated the hypothesis
one-directionally in a fixed reference `p°`:

  > `D(x, p°, ξ₁) = D(x, p°, ξ₂) ⇒ D(x, p, ξ₁) = D(x, p, ξ₂)`.

This is `LevelSetsRefine` below. It suffices for part (a), but **not for
part (b)**: the proof step "apply the hypothesis with `P*` in place of
`p°`" silently treated the hypothesis as symmetric. The counterexample
`refine_only_breaks_unique_recovery` exhibits a `D` where the one-directional
hypothesis holds at `p° = false` but single-observation recovery fails at
`P* = true`. We retain the two definitions and the counterexample as
documentation of why the symmetric strengthening matters.
-/

namespace CausalLadder.IndexStructure

variable {X P Ξ Q : Type*}

/-- **One-directional hypothesis** as stated in the paper: level sets at the
reference price `p°` refine level sets at every other `p`. -/
def LevelSetsRefine (D : X → P → Ξ → Q) (p_zero : P) : Prop :=
  ∀ x p ξ₁ ξ₂, D x p_zero ξ₁ = D x p_zero ξ₂ → D x p ξ₁ = D x p ξ₂

/-- **Symmetric hypothesis** needed for part (b): level sets of
`ξ ↦ D(x, p, ξ)` are the same for every `p`. -/
def LevelSetsAgree (D : X → P → Ξ → Q) : Prop :=
  ∀ x p₁ p₂ ξ₁ ξ₂, D x p₁ ξ₁ = D x p₁ ξ₂ → D x p₂ ξ₁ = D x p₂ ξ₂

/-- `LevelSetsAgree` implies `LevelSetsRefine` for any reference price. -/
lemma LevelSetsAgree.toRefine
    {D : X → P → Ξ → Q} (h : LevelSetsAgree D) (p_zero : P) :
    LevelSetsRefine D p_zero :=
  fun x p ξ₁ ξ₂ hp_zero => h x p_zero p ξ₁ ξ₂ hp_zero

/-- **Part (a) — existence of the index factorization.**

Given the as-stated (one-directional) hypothesis `LevelSetsRefine`, the demand
function factors as `D(x, p, ξ) = H(δ(x, ξ), p, x)` where
`δ(x, ξ) := D(x, p°, ξ)`.

Source: `paper/paper.tex` lines 791–793. -/
theorem index_structure_part_a
    [Nonempty Q]
    (D : X → P → Ξ → Q) (p_zero : P)
    (hD : LevelSetsRefine D p_zero) :
    ∃ H : Q → P → X → Q, ∀ x p ξ, D x p ξ = H (D x p_zero ξ) p x := by
  classical
  refine ⟨fun q p x =>
    if h : ∃ ξ, D x p_zero ξ = q then D x p h.choose else Classical.arbitrary Q,
    ?_⟩
  intros x p ξ
  have hex : ∃ ξ', D x p_zero ξ' = D x p_zero ξ := ⟨ξ, rfl⟩
  show D x p ξ = (if h : ∃ ξ', D x p_zero ξ' = D x p_zero ξ then
                    D x p h.choose else Classical.arbitrary Q)
  rw [dif_pos hex]
  exact (hD x p hex.choose ξ hex.choose_spec).symm

/-- **Part (a) under the canonical symmetric hypothesis.** Convenience
wrapper: `LevelSetsAgree` implies `LevelSetsRefine p_zero` for any
`p_zero`, so the factorization result carries over directly. -/
theorem index_structure_part_a_symmetric
    [Nonempty Q]
    (D : X → P → Ξ → Q) (p_zero : P)
    (hD : LevelSetsAgree D) :
    ∃ H : Q → P → X → Q, ∀ x p ξ, D x p ξ = H (D x p_zero ξ) p x :=
  index_structure_part_a D p_zero (hD.toRefine p_zero)

/-- **Part (b) under the symmetric hypothesis — unique recovery.**

If the level-set structure is the same at every price (`LevelSetsAgree`),
then any single observation `(x, P*, Q*)` pins down the index `δ(x, ξ̄)`
uniquely.

Source: `paper/paper.tex` lines 794–796 (the proof gap is patched here by
strengthening the hypothesis). -/
theorem level_sets_agree_part_b
    (D : X → P → Ξ → Q)
    (hD : LevelSetsAgree D)
    (x : X) (P_star p_zero : P)
    (ξ₁ ξ₂ : Ξ) (hQ : D x P_star ξ₁ = D x P_star ξ₂) :
    D x p_zero ξ₁ = D x p_zero ξ₂ :=
  hD x P_star p_zero ξ₁ ξ₂ hQ

/-- **Counterexample to part (b) under the literal one-directional hypothesis.**

We exhibit a concrete `D : Unit → Bool → ℕ → ℕ` for which:
* `LevelSetsRefine D false` holds (the hypothesis as stated in the paper),
* yet two distinct `ξ` values share the same `D(x, true, ξ)` while
  giving different `D(x, false, ξ)`.

The construction:
* `D ⟨⟩ false ξ = ξ` (at `p° = false`, level sets are singletons — finest),
* `D ⟨⟩ true ξ = 0` (at `P* = true`, level sets are all of `ℕ` — coarsest).

`LevelSetsRefine` holds vacuously at `p° = false`: the only way
`D ⟨⟩ false ξ₁ = D ⟨⟩ false ξ₂` is `ξ₁ = ξ₂`, which trivially gives equality
at any `p`. But at `P* = true`, all `ξ` collapse to `0`, while at `p°` they
remain distinct. So a single observation at `P*` cannot recover
`δ(x, ξ̄) = D(x, p°, ξ̄)`. -/
theorem refine_only_breaks_unique_recovery :
    ∃ (D : Unit → Bool → ℕ → ℕ) (p_zero : Bool) (P_star : Bool)
      (x : Unit) (ξ₁ ξ₂ : ℕ),
      LevelSetsRefine D p_zero ∧
      D x P_star ξ₁ = D x P_star ξ₂ ∧
      D x p_zero ξ₁ ≠ D x p_zero ξ₂ := by
  refine ⟨fun _ p ξ => if p then 0 else ξ, false, true, ⟨⟩, 1, 2, ?_, ?_, ?_⟩
  · -- LevelSetsRefine at p_zero = false: D ⟨⟩ false ξ₁ = D ⟨⟩ false ξ₂ means
    -- ξ₁ = ξ₂, which gives equality at any p.
    intro _ p ξ₁ ξ₂ h
    -- h : (if false then 0 else ξ₁) = (if false then 0 else ξ₂), i.e., ξ₁ = ξ₂
    simp at h
    subst h
    rfl
  · -- D ⟨⟩ true 1 = D ⟨⟩ true 2: both equal 0.
    rfl
  · -- D ⟨⟩ false 1 = 1 ≠ 2 = D ⟨⟩ false 2.
    decide

end CausalLadder.IndexStructure
