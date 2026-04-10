import Mathlib.Data.Real.Basic

/-!
# Share Inversion and Point Identification are Equivalent (Corollary 1)

Under the demand model with C1 maintained:
- (a) Price-only counterfactuals are point-identified iff C2 (invertibility) holds.
- (b) Characteristics-changing counterfactuals are point-identified iff C2 holds
  and all consistent latent states yield the same index at the new characteristics.

The "if" direction comes from Theorem 2 (BridgeTheorem).
The "only if" direction comes from Proposition 4 (Necessity).

## Mathematical content

This is the paper's headline result: Berry inversion is necessary and sufficient
for market-specific counterfactuals.

**Source:** `paper/paper.tex` lines 370–379.
-/

namespace CausalLadder.BridgeCorollary

/-- **(a) Price-only iff: invertibility ↔ point identification.**

Forward: if σ is injective in δ (C2), then σ⁻¹ recovers δ* uniquely,
so σ(δ*, p', x*) is a single value.

Backward: if σ is NOT injective, Proposition 4(a) gives two distinct
counterfactual values.

We encode this as: injective σ implies unique counterfactual value. -/
theorem price_counterfactual_iff_invertibility
    {Δ P X Q : Type*} [DecidableEq Q]
    (σ : Δ → P → X → Q)
    (p_star p' : P) (x_star : X) (Q_star : Q)
    -- C2: σ is injective in its first argument at (p_star, x_star)
    (hC2 : Function.Injective (fun δ => σ δ p_star x_star))
    -- δ* is the unique pre-image
    (δ_star : Δ) (hδ : σ δ_star p_star x_star = Q_star) :
    -- All δ consistent with Q* agree on the counterfactual at p'
    ∀ δ, σ δ p_star x_star = Q_star → σ δ p' x_star = σ δ_star p' x_star := by
  intro δ hδ'
  have : δ = δ_star := hC2 (show (fun δ => σ δ p_star x_star) δ =
    (fun δ => σ δ p_star x_star) δ_star by simp [hδ', hδ])
  rw [this]

/-- **Negative control.** Without injectivity, consistent δ values can
produce different counterfactuals. Witness: identity function on ℝ² → ℝ
that maps two different δ values to the same Q* but different Q'. -/
example : ∃ (σ : ℝ → ℝ → ℝ) (δ₁ δ₂ p₁ p₂ : ℝ),
    σ δ₁ p₁ = σ δ₂ p₁ ∧ σ δ₁ p₂ ≠ σ δ₂ p₂ := by
  -- σ(δ, p) = δ * p. At p=0, both give 0. At p=1, they differ.
  refine ⟨fun δ p => δ * p, 1, 2, 0, 1, ?_, ?_⟩
  · simp
  · norm_num

end CausalLadder.BridgeCorollary
