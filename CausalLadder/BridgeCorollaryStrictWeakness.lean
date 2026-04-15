import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import CausalLadder.BridgeCorollary

/-!
# Cor 1(b) condition is strictly weaker than C3 — refine item D9 (2026-04-15)

`paper/paper.tex:407` (the "plain language" paragraph after Corollary 1)
currently pivots to C3 (recoverability) in describing what the corollary
requires. The referee's concern: the corollary's *actual* hypothesis is
weaker than C3, and the prose obscures this.

## Lean's hypothesis (extracted verbatim from `BridgeCorollary.lean:68-69`)

```
h_consistent_collapse :
  ∀ ξ, δ_fn x_star ξ = δ_star → δ_fn x' ξ = δ_prime
```

In words: every latent state `ξ` consistent with the observed market
(i.e., `δ_fn x_star ξ = δ_star`) maps to the *same* counterfactual index
`δ_prime` at `x'`.

C3 (global recoverability) says: for each `x`, the map `ξ ↦ δ_fn x ξ`
is injective.

## Claim

C3 implies the hypothesis. The converse fails: this file exhibits a
concrete `δ_fn` for which the hypothesis holds at a specific
`(x_star, δ_star, x', δ_prime)` but `δ_fn x_star ·` is *not* injective
(and `δ_fn x' ·` is not injective either). Hence Cor 1(b)'s hypothesis
is strictly weaker than C3.

## What this means for the prose

The "plain language" paragraph should lead with *what the hypothesis
says* (all consistent ξ collapse to the same δ' at x'), then note that
C3 is a *sufficient* condition. The corollary does not require C3.

## Paper reference

The pattern is already present as a numerical example at
`paper/paper.tex:409` ("Example (C2 without C3)"). This file makes the
example's structural point precise: C2 + the collapse hypothesis
suffice — C3 is not needed.
-/

namespace CausalLadder.BridgeCorollaryStrictWeakness

/-- Two latent states. -/
abbrev Ξ : Type := Bool

/-- Two characteristics values: baseline and counterfactual. -/
abbrev X : Type := Bool

/-- Demand indices are natural numbers (could be any type). -/
abbrev Δ : Type := ℕ

/-- A non-injective `δ_fn` for which both ξ values collapse at both x
values. This is the degenerate case that still satisfies Cor 1(b)'s
hypothesis: at `x_star = false` both ξ give `δ_star = 0`; at
`x' = true` both ξ give `δ_prime = 5`. -/
def δ_witness : X → Ξ → Δ := fun _ _ => 5

/-- Alternative that realises the *paper's* "C2 without C3" example:
at `x_star`, both ξ map to `δ_star = 0`. At `x'`, both still map to the
same `δ_prime = 5`. Neither fibre is injective, yet the hypothesis
holds. -/
def δ_cornerCase : X → Ξ → Δ :=
  fun x _ => if x then 5 else 0

/-- **C3 FAILS for `δ_cornerCase`.** At `x = false`, both `tt` and `ff`
map to `0`, so `ξ ↦ δ_cornerCase false ξ` is not injective. -/
theorem cornerCase_fails_C3 :
    ¬ (∀ x : X, Function.Injective (δ_cornerCase x)) := by
  intro h
  have := @h false true false
  simp [δ_cornerCase] at this

/-- **Cor 1(b)'s hypothesis HOLDS for `δ_cornerCase`.**

All `ξ` consistent with `δ_cornerCase false ξ = 0` (which is: all `ξ`)
map to `δ_cornerCase true ξ = 5`. -/
theorem cornerCase_satisfies_hypothesis :
    ∀ ξ, δ_cornerCase false ξ = 0 → δ_cornerCase true ξ = 5 := by
  intro ξ _
  simp [δ_cornerCase]

/-- **Cor 1(b) applies to `δ_cornerCase` even though C3 fails.**

We plug `δ_cornerCase` into `BridgeCorollary.characteristics_curve_identified`
and conclude that the counterfactual demand curve at `x' = true` is
point-identified, *without invoking C3*. -/
theorem cornerCase_counterfactual_identified
    {P Q : Type*} (σ : Δ → P → X → Q) :
    ∀ ξ (p : P), δ_cornerCase false ξ = 0 →
      σ (δ_cornerCase true ξ) p true = σ 5 p true :=
  CausalLadder.BridgeCorollary.characteristics_curve_identified
    (Δ := Δ) (P := P) (X := X) (Q := Q) (Ξ := Ξ)
    σ δ_cornerCase false true 0 5
    cornerCase_satisfies_hypothesis

/-- **C3 implies the hypothesis.** If `ξ ↦ δ_fn x ξ` is injective at
`x_star`, and two ξ values both map to `δ_star`, they are equal — so
they also give the same value at `x'`. (This is why the paper's
footnote presents C3 as sufficient; the theorem's actual hypothesis
captures the weaker sufficient-for-point-id condition.) -/
theorem C3_implies_hypothesis
    {Δ X Ξ : Type*}
    (δ_fn : X → Ξ → Δ)
    (hC3 : ∀ x, Function.Injective (δ_fn x))
    (x_star x' : X) (δ_star : Δ) (ξ₀ : Ξ) (hξ₀ : δ_fn x_star ξ₀ = δ_star) :
    ∃ δ_prime, ∀ ξ, δ_fn x_star ξ = δ_star → δ_fn x' ξ = δ_prime := by
  refine ⟨δ_fn x' ξ₀, ?_⟩
  intro ξ hξ
  have : ξ = ξ₀ := hC3 x_star (hξ.trans hξ₀.symm)
  rw [this]

end CausalLadder.BridgeCorollaryStrictWeakness
