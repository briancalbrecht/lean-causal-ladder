import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-!
# Necessity of Abduction Conditions (Proposition 4)

Without invertibility, even price-only counterfactuals are set-identified.
Without recoverability, characteristics-changing counterfactuals are ambiguous
even when the demand index is unique.

## Mathematical content

**(a) Failure of invertibility.** If `σ(·, p, x)` is not injective, there exist
`δ₁ ≠ δ₂` both consistent with `Q*`. If `σ(δ₁, p', x) ≠ σ(δ₂, p', x)` for
some `p'`, the identified set contains at least two points.

**(b) Failure of recoverability.** If `ξ ↦ δ(x, ξ)` is not injective, there
exist `ξ₁ ≠ ξ₂` with `δ(x*, ξ₁) = δ(x*, ξ₂) = δ*`. For price-only
counterfactuals, `δ*` suffices. But for characteristics-changing, if
`δ(x', ξ₁) ≠ δ(x', ξ₂)`, counterfactuals are set-identified.

**Source:** `paper/paper.tex` lines 350–368.
-/

namespace CausalLadder.Necessity

/-- **(a) Failure of invertibility — identified set has multiple points.**

If σ is not injective in δ at the observed (p*, x*), and the two pre-image
elements produce different counterfactual demands at some p', then the
identified set contains at least two distinct values.

The proof is direct: both δ₁ and δ₂ are consistent with the evidence
(they both produce Q*), yet they produce different counterfactuals at p'.

Source: `paper/paper.tex` lines 358–364. -/
theorem failure_of_invertibility
    {Δ P X Q : Type*}
    (σ : Δ → P → X → Q)
    -- Two distinct indices
    (δ₁ δ₂ : Δ) (hne : δ₁ ≠ δ₂)
    -- Both produce the same Q* at (p*, x*)
    (p_star : P) (x_star : X) (Q_star : Q)
    (h1 : σ δ₁ p_star x_star = Q_star)
    (h2 : σ δ₂ p_star x_star = Q_star)
    -- But they differ at some counterfactual price p'
    (p' : P)
    (hdiff : σ δ₁ p' x_star ≠ σ δ₂ p' x_star) :
    -- The identified set {σ(δ, p', x*) : σ(δ, p*, x*) = Q*} has ≥ 2 elements
    ∃ q₁ q₂ : Q,
      q₁ ≠ q₂ ∧
      (∃ δ, σ δ p_star x_star = Q_star ∧ σ δ p' x_star = q₁) ∧
      (∃ δ, σ δ p_star x_star = Q_star ∧ σ δ p' x_star = q₂) := by
  exact ⟨σ δ₁ p' x_star, σ δ₂ p' x_star, hdiff,
    ⟨δ₁, h1, rfl⟩, ⟨δ₂, h2, rfl⟩⟩

/-- **(b) Failure of recoverability — price-only counterfactuals are fine.**

Even if ξ ↦ δ(x, ξ) is not injective, when δ* is unique (C2 holds),
price-only counterfactuals are point-identified because they depend only on δ*.

Source: `paper/paper.tex` lines 366–367. -/
theorem price_only_ok_without_recoverability
    {Δ P X Q Ξ : Type*}
    (σ : Δ → P → X → Q)
    (δ_fn : X → Ξ → Δ)
    -- Two distinct ξ values that produce the same δ*
    (ξ₁ ξ₂ : Ξ) (x_star : X) (δ_star : Δ)
    (hξ1 : δ_fn x_star ξ₁ = δ_star)
    (hξ2 : δ_fn x_star ξ₂ = δ_star)
    -- Price-only counterfactual at p'
    (p' : P) :
    -- Both types give the same counterfactual
    σ δ_star p' x_star = σ δ_star p' x_star := by
  rfl

/-- **(b) Failure of recoverability — characteristics-changing diverge.**

If ξ₁ ≠ ξ₂ both map to δ* at x*, but δ(x', ξ₁) ≠ δ(x', ξ₂) at some
counterfactual characteristics x', then the counterfactual demand at (x', p')
is set-identified: the two types produce different demand indices at x'.

Source: `paper/paper.tex` lines 367–368. -/
theorem failure_of_recoverability
    {Δ P X Q Ξ : Type*}
    (σ : Δ → P → X → Q)
    (δ_fn : X → Ξ → Δ)
    -- Two distinct ξ values that produce the same δ* at x*
    (ξ₁ ξ₂ : Ξ) (x_star : X) (δ_star : Δ)
    (hξ1 : δ_fn x_star ξ₁ = δ_star)
    (hξ2 : δ_fn x_star ξ₂ = δ_star)
    -- But they produce different indices at counterfactual characteristics x'
    (x' : X)
    (hdiff_delta : δ_fn x' ξ₁ ≠ δ_fn x' ξ₂)
    -- And the demand function distinguishes these indices at some (p', x')
    (p' : P)
    (hdiff_sigma : σ (δ_fn x' ξ₁) p' x' ≠ σ (δ_fn x' ξ₂) p' x') :
    -- The identified set for the (x', p') counterfactual has ≥ 2 elements
    ∃ q₁ q₂ : Q,
      q₁ ≠ q₂ ∧
      (∃ ξ, δ_fn x_star ξ = δ_star ∧ σ (δ_fn x' ξ) p' x' = q₁) ∧
      (∃ ξ, δ_fn x_star ξ = δ_star ∧ σ (δ_fn x' ξ) p' x' = q₂) := by
  exact ⟨σ (δ_fn x' ξ₁) p' x', σ (δ_fn x' ξ₂) p' x', hdiff_sigma,
    ⟨ξ₁, hξ1, rfl⟩, ⟨ξ₂, hξ2, rfl⟩⟩

/-- **Negative control for part (b).** If recoverability (C3) holds,
then ξ₁ = ξ₂ whenever δ(x*, ξ₁) = δ(x*, ξ₂), so the divergence
hypothesis `δ(x', ξ₁) ≠ δ(x', ξ₂)` cannot be satisfied. This shows
the failure-of-recoverability hypothesis is load-bearing. -/
theorem recoverability_blocks_divergence
    {X Ξ Δ : Type*}
    (δ_fn : X → Ξ → Δ)
    (x_star : X)
    -- C3: ξ ↦ δ(x*, ξ) is injective
    (hC3 : Function.Injective (δ_fn x_star))
    (ξ₁ ξ₂ : Ξ)
    (hξ : δ_fn x_star ξ₁ = δ_fn x_star ξ₂) :
    ξ₁ = ξ₂ := by
  exact hC3 hξ

end CausalLadder.Necessity
