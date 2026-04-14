import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

/-!
# Necessity of Abduction Conditions (Proposition `p:necessity`)

Without invertibility, even price-only counterfactuals are set-identified.
Without recoverability — *given* invertibility — characteristics-changing
counterfactuals are not point-identified at any price.

## Mathematical content

**(a) Failure of invertibility.** If `σ(·, p, x)` is not injective at the
observed `(p*, x*)`, there exist `δ₁ ≠ δ₂` both consistent with `Q*`. If
`σ(δ₁, p̃, x*) ≠ σ(δ₂, p̃, x*)` for some witness price `p̃`, the identified
set at `p̃` contains at least two points.

**(b) Failure of recoverability, conditional on invertibility.** Suppose
C2 holds (`σ(·, p', x')` is injective at every `(p', x')`). If
`ξ ↦ δ(x, ξ)` is not injective and the pre-image elements separate at
some counterfactual characteristics — i.e., there exist `ξ₁ ≠ ξ₂` with
`δ(X*, ξ_k) = δ*` and `δ(x', ξ₁) ≠ δ(x', ξ₂)` for some `x'` — then C2's
injectivity propagates the index disequality to *demand* disequality at
every price. The counterfactual demand curve `p ↦ D(x', p, ξ̄)` is not
point-identified at any price.

**Source:** `paper/paper.tex` lines 371–386 (post-2026-04-14 strengthening
of part (b) following the ChatGPT Pro adversarial review and the
companion Lean audit).
-/

namespace CausalLadder.Necessity

/-- **(a) Failure of invertibility — identified set at the witness price
has multiple points.**

If σ is not injective in δ at the observed (p*, x*), and the two pre-image
elements produce different counterfactual demands at *some* witness price
`p̃`, then the identified set at `p̃` contains at least two distinct values.

The proof is direct: both δ₁ and δ₂ are consistent with the evidence
(they both produce Q*), yet they produce different counterfactuals at p̃.

Source: `paper/paper.tex` line 371 (witness-price formulation, post-rename
to `p̃`). -/
theorem failure_of_invertibility
    {Δ P X Q : Type*}
    (σ : Δ → P → X → Q)
    -- Two distinct indices
    (δ₁ δ₂ : Δ) (hne : δ₁ ≠ δ₂)
    -- Both produce the same Q* at (p*, x*)
    (p_star : P) (x_star : X) (Q_star : Q)
    (h1 : σ δ₁ p_star x_star = Q_star)
    (h2 : σ δ₂ p_star x_star = Q_star)
    -- They differ at some witness price p̃
    (p_tilde : P)
    (hdiff : σ δ₁ p_tilde x_star ≠ σ δ₂ p_tilde x_star) :
    -- The identified set {σ(δ, p̃, x*) : σ(δ, p*, x*) = Q*} has ≥ 2 elements
    ∃ q₁ q₂ : Q,
      q₁ ≠ q₂ ∧
      (∃ δ, σ δ p_star x_star = Q_star ∧ σ δ p_tilde x_star = q₁) ∧
      (∃ δ, σ δ p_star x_star = Q_star ∧ σ δ p_tilde x_star = q₂) := by
  exact ⟨σ δ₁ p_tilde x_star, σ δ₂ p_tilde x_star, hdiff,
    ⟨δ₁, h1, rfl⟩, ⟨δ₂, h2, rfl⟩⟩

/-- **(b, side fact) Failure of recoverability — price-only counterfactuals
are fine.**

Even if ξ ↦ δ(x*, ξ) is not injective, when δ* is unique (C2 holds),
price-only counterfactuals at the observed characteristics are
point-identified because they depend only on δ*.

Source: `paper/paper.tex` line 385 ("for a price-only counterfactual,
δ* is sufficient"). -/
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

/-- **(b) Failure of recoverability, conditional on C2 — characteristics-
changing demand curve is not point-identified at any price.**

Strengthened formulation (paper line 372, post-2026-04-14):

Hypotheses:
* C2: `σ(·, p', x')` is injective in δ at every `(p', x')`.
* Two distinct `ξ₁ ≠ ξ₂` in supp(ξ ∣ X*) with `δ(X*, ξ_k) = δ*` for both.
* They separate at some counterfactual characteristics: `δ(x', ξ₁) ≠ δ(x', ξ₂)`.

Conclusion: at *every* price `p'`, the identified set at `(x', p')`
contains at least two distinct demand values. (Earlier, weaker formulation
took σ-disequality at some `(x', p')` as a hypothesis and concluded
set-identification at that single `(x', p')` — true but tautological.
The ChatGPT Pro review on 2026-04-14 flagged this; the strengthening uses
C2's injectivity to *derive* σ-disequality at every `p'` from
δ-disequality at `x'`.)

Source: `paper/paper.tex` lines 372 + 384. -/
theorem failure_of_recoverability
    {Δ P X Q Ξ : Type*}
    (σ : Δ → P → X → Q)
    (δ_fn : X → Ξ → Δ)
    -- C2: σ(·, p', x') is injective at every (p', x')
    (hC2 : ∀ p' x', Function.Injective (fun δ => σ δ p' x'))
    -- Two distinct ξ values that produce the same δ* at x*
    (ξ₁ ξ₂ : Ξ) (hξne : ξ₁ ≠ ξ₂)
    (x_star : X) (δ_star : Δ)
    (hξ1 : δ_fn x_star ξ₁ = δ_star)
    (hξ2 : δ_fn x_star ξ₂ = δ_star)
    -- They produce different indices at counterfactual characteristics x'
    (x' : X)
    (hdiff_delta : δ_fn x' ξ₁ ≠ δ_fn x' ξ₂) :
    -- At EVERY p', the identified set at (x', p') contains ≥ 2 elements
    ∀ p' : P,
      ∃ q₁ q₂ : Q,
        q₁ ≠ q₂ ∧
        (∃ ξ, δ_fn x_star ξ = δ_star ∧ σ (δ_fn x' ξ) p' x' = q₁) ∧
        (∃ ξ, δ_fn x_star ξ = δ_star ∧ σ (δ_fn x' ξ) p' x' = q₂) := by
  intro p'
  -- The key step: lift δ-disequality at x' to σ-disequality at every p'
  -- using C2's injectivity at (p', x').
  have hdiff_sigma : σ (δ_fn x' ξ₁) p' x' ≠ σ (δ_fn x' ξ₂) p' x' :=
    fun heq => hdiff_delta (hC2 p' x' heq)
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
