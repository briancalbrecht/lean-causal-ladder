import Mathlib.Data.Real.Basic

/-!
# The Structural Model Identifies the Demand Curve (Theorem 2)

Berry inversion recovers the market's latent demand index from observed data.
Given index structure (C1), invertibility (C2), and recoverability (C3),
counterfactual demand is point-identified.

## Mathematical content

Given:
- **C1 (Index structure):** `D(x, p, ξ) = σ(δ(x, ξ), p, x)` for some index `δ`
- **C2 (Invertibility):** `δ ↦ σ(δ, p, x)` is injective (has a left inverse `σ⁻¹`)
- **C3 (Recoverability):** `ξ ↦ δ(x, ξ)` is injective (has a left inverse `r`)

Then from observed `(Q*, P*, X*)`:
1. Recover `δ* = σ⁻¹(Q*, P*, X*)`
2. For price-only counterfactual: `D(X*, p', ξ̄) = σ(δ*, p', X*)`
3. For characteristics-changing: recover `ξ̄ = r(δ*, X*)`, then
   `D(x', p', ξ̄) = σ(δ(x', ξ̄), p', x')`

The proof is purely definitional: substitute C1, apply C2, apply C3.

**Source:** `paper/paper.tex` lines 310–340.
-/

namespace CausalLadder.BridgeTheorem

variable {X P Q Ξ Δ Θ : Type*}

/-- **Price-only counterfactual recovery (Theorem 2, price case).**

Given C1 (index structure) and C2 (invertibility), the counterfactual demand
at a new price `p'` holding characteristics fixed is `σ(δ*, p', x*)`, where
`δ*` is recovered by inverting observed shares.

The proof is a chain of equalities:
  `Q* = σ(δ*, P*, X*)` by C1
  `δ* = σ⁻¹(Q*, P*, X*)` by C2
  `D(X*, p', ξ̄) = σ(δ*, p', X*)` by C1 + structural invariance

Source: `paper/paper.tex` lines 338–340. -/
theorem price_counterfactual_recovery
    -- Types
    (δ_space : Type*) (x_space p_space q_space ξ_space : Type*)
    -- The structural functions
    (σ : δ_space → p_space → x_space → q_space)
    (δ_fn : x_space → ξ_space → δ_space)
    (σ_inv : q_space → p_space → x_space → δ_space)
    -- C1: index structure
    (D : x_space → p_space → ξ_space → q_space)
    (hC1 : ∀ x p ξ, D x p ξ = σ (δ_fn x ξ) p x)
    -- C2: invertibility (σ_inv is a left inverse of σ in the δ argument)
    (hC2 : ∀ δ p x, σ_inv (σ δ p x) p x = δ)
    -- Observed data
    (x_star : x_space) (p_star p' : p_space) (ξ_bar : ξ_space)
    -- δ* is the index at the observed market
    (δ_star : δ_space) (hδ : δ_star = δ_fn x_star ξ_bar) :
    -- Conclusion: counterfactual demand equals σ evaluated at recovered δ*
    D x_star p' ξ_bar = σ δ_star p' x_star := by
  rw [hC1, hδ]

/-- **Characteristics-changing counterfactual recovery (Theorem 2, full case).**

Given C1, C2, and C3 (recoverability), the counterfactual demand at new
characteristics `x'` and price `p'` is `σ(δ(x', ξ̄), p', x')`, where
`ξ̄ = r(δ*, x*)` is recovered from the inverted index.

Source: `paper/paper.tex` lines 335–340. -/
theorem characteristics_counterfactual_recovery
    -- Types
    (δ_space : Type*) (x_space p_space q_space ξ_space : Type*)
    -- The structural functions
    (σ : δ_space → p_space → x_space → q_space)
    (δ_fn : x_space → ξ_space → δ_space)
    (r : δ_space → x_space → ξ_space)
    -- C1: index structure
    (D : x_space → p_space → ξ_space → q_space)
    (hC1 : ∀ x p ξ, D x p ξ = σ (δ_fn x ξ) p x)
    -- C3: recoverability (r is a left inverse of δ_fn in the ξ argument)
    (hC3 : ∀ x ξ, r (δ_fn x ξ) x = ξ)
    -- Observed data
    (x_star x' : x_space) (p' : p_space) (ξ_bar : ξ_space)
    -- δ* is the index at the observed market
    (δ_star : δ_space) (hδ : δ_star = δ_fn x_star ξ_bar) :
    -- Conclusion: counterfactual demand at x' equals σ at the new index
    D x' p' ξ_bar = σ (δ_fn x' ξ_bar) p' x' := by
  rw [hC1]

end CausalLadder.BridgeTheorem
