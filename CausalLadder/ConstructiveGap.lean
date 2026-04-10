import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Constructive Experimental–Structural Gap (Proposition 1)

Two linear demand curves with different slopes cross at the observed equilibrium
price. At any other price, they diverge. An experiment that averages over
markets cannot determine which curve generated the observed data.

## Mathematical content

Given `D(p, ξₖ) = α(ξₖ) - β(ξₖ) · p` with `β(ξ₁) ≠ β(ξ₂)`:

**(a) Observational equivalence.** The crossing price is
`P* = (α₁ - α₂) / (β₁ - β₂)`, yielding common quantity `Q* = α₁ - β₁ · P*`.
Concretely: α₁=12, β₁=3, α₂=6, β₂=1 gives P*=3, Q*=3.

**(b) Counterfactual divergence.** For all `p' ≠ P*`,
`D(p', ξ₁) - D(p', ξ₂) = (β₁ - β₂)(P* - p') ≠ 0`.

**(c) Experimental insufficiency.** The identified set contains both
`D(p', ξ₁)` and `D(p', ξ₂)`, hence more than one point.

**Source:** `paper/paper.tex` lines 117–138.
-/

namespace CausalLadder.ConstructiveGap

/-- Linear demand function: `D(p, α, β) = α - β * p`. -/
def D (p α β : ℝ) : ℝ := α - β * p

/-- **(a) Observational equivalence — concrete witness.**
With α₁=12, β₁=3, α₂=6, β₂=1, the crossing price is P*=3 and Q*=3.
Both demand curves produce the same (Q*, P*).

Source: `paper/paper.tex` line 133. -/
theorem observational_equivalence :
    D 3 12 3 = 3 ∧ D 3 6 1 = 3 := by
  unfold D
  constructor <;> ring

/-- **(a) Observational equivalence — general.**
If `P* = (α₁ - α₂) / (β₁ - β₂)`, then `D(P*, α₁, β₁) = D(P*, α₂, β₂)`.

Source: `paper/paper.tex` line 133. -/
theorem crossing_at_Pstar
    (α₁ β₁ α₂ β₂ : ℝ) (hβ : β₁ ≠ β₂)
    (Pstar : ℝ) (hP : Pstar = (α₁ - α₂) / (β₁ - β₂)) :
    D Pstar α₁ β₁ = D Pstar α₂ β₂ := by
  unfold D
  have hβ_ne : (β₁ - β₂) ≠ 0 := sub_ne_zero.mpr hβ
  suffices h : (α₁ - β₁ * Pstar) - (α₂ - β₂ * Pstar) = 0 by linarith
  rw [hP]
  have : (β₁ - β₂) * ((α₁ - α₂) / (β₁ - β₂)) = α₁ - α₂ :=
    mul_div_cancel₀ _ hβ_ne
  linarith

/-- **(b) Counterfactual divergence.**
If two linear demand curves cross at `P*` (same quantity) and have different
slopes (`β₁ ≠ β₂`), then at any `p' ≠ P*` their demands differ.

The difference is `(β₁ - β₂)(P* - p')`, which is nonzero when both
`β₁ ≠ β₂` and `p' ≠ P*`.

Source: `paper/paper.tex` lines 135–136. -/
theorem counterfactual_divergence
    (α₁ β₁ α₂ β₂ Pstar p' : ℝ)
    (hβ : β₁ ≠ β₂)
    (hp : p' ≠ Pstar)
    (hcross : D Pstar α₁ β₁ = D Pstar α₂ β₂) :
    D p' α₁ β₁ ≠ D p' α₂ β₂ := by
  unfold D at *
  intro heq
  have h1 : α₁ - β₁ * Pstar = α₂ - β₂ * Pstar := hcross
  have h2 : α₁ - β₁ * p' = α₂ - β₂ * p' := heq
  have h3 : (β₁ - β₂) * (p' - Pstar) = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h | h
  · exact hβ (sub_eq_zero.mp h)
  · exact hp (by linarith [sub_eq_zero.mp h])

/-- **(b) Counterfactual divergence — concrete.**
At p'=4: D(4, ξ₁) = 0, D(4, ξ₂) = 2.

Source: `paper/paper.tex` line 135. -/
theorem concrete_divergence :
    D 4 12 3 = 0 ∧ D 4 6 1 = 2 := by
  unfold D
  constructor <;> ring

/-- **Negative control.** If slopes are equal (`β₁ = β₂`), crossing implies
identical curves everywhere, so divergence fails. This shows `β₁ ≠ β₂`
is load-bearing. -/
example : ∃ α₁ α₂ β Pstar p' : ℝ,
    p' ≠ Pstar ∧
    D Pstar α₁ β = D Pstar α₂ β ∧
    D p' α₁ β = D p' α₂ β := by
  refine ⟨5, 5, 1, 0, 1, by norm_num, ?_, ?_⟩ <;> unfold D <;> ring

end CausalLadder.ConstructiveGap
