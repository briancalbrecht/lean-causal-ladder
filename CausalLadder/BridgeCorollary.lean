import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic

/-!
# Share Inversion and Point Identification are Equivalent (`c:bridge`)

Under the demand model with C1 maintained:
- (a) The price-only **demand curve** `p ↦ D(X*, p, ξ̄)` is point-identified
  iff C2 (invertibility) holds.
- (b) Given C2, the **demand curve** `p ↦ D(x', p, ξ̄)` at counterfactual
  characteristics `x'` is point-identified iff all consistent ξ yield the
  same `δ(x', ξ)`.

Both parts are at the **curve level**, not pointwise. The pre-2026-04-14
pointwise iff was false at single counterfactual prices (e.g.,
`D(p, ξ) = 10 + p(p-1)ξ` has C2 failing yet `D(1, ξ) = 10` for both ξ
values, so the pointwise counterfactual at `p' = 1` is point-identified
even without C2).

**Source:** `paper/paper.tex` lines 388–405 (post-2026-04-14 edits
following the ChatGPT Pro adversarial review).
-/

namespace CausalLadder.BridgeCorollary

/-- **(a) Curve-level iff: invertibility ↔ point identification of the
price-only demand curve.**

If σ is injective in δ at every (p, x*), then σ⁻¹ recovers δ* uniquely,
and the entire price-only demand curve `p ↦ σ(δ, p, X*)` is determined:
all consistent δ are equal to δ*, so they map to the same value at every p.

The "only if" direction lives in `Necessity.failure_of_invertibility`:
if C2 fails at the observation, there is a witness price at which two
consistent δ values produce different demands, so the curve is not
point-identified.

We encode the curve-level "if" direction here: under C2, all consistent
δ produce the *same demand at every price*. -/
theorem price_curve_identified_under_C2
    {Δ P X Q : Type*}
    (σ : Δ → P → X → Q)
    (p_star : P) (x_star : X) (Q_star : Q)
    -- C2: σ(·, p_star, x_star) is injective at the observation
    (hC2 : Function.Injective (fun δ => σ δ p_star x_star))
    -- δ* is the unique pre-image
    (δ_star : Δ) (hδ : σ δ_star p_star x_star = Q_star) :
    -- All δ consistent with Q* agree on the WHOLE price curve
    ∀ δ, σ δ p_star x_star = Q_star → ∀ p, σ δ p x_star = σ δ_star p x_star := by
  intro δ hδ' p
  have hδeq : δ = δ_star :=
    hC2 (show (fun δ => σ δ p_star x_star) δ =
      (fun δ => σ δ p_star x_star) δ_star by simp [hδ', hδ])
  rw [hδeq]

/-- **(b) Curve-level iff (if direction): if all consistent ξ yield the
same δ(x', ξ), then the counterfactual demand curve at x' is identified
at every p.**

Source: `paper/paper.tex` line 392 + 404. -/
theorem characteristics_curve_identified
    {Δ P X Q Ξ : Type*}
    (σ : Δ → P → X → Q)
    (δ_fn : X → Ξ → Δ)
    (x_star x' : X) (δ_star : Δ)
    -- All consistent ξ yield the same δ' ≡ δ(x', ξ)
    (δ_prime : Δ)
    (h_consistent_collapse :
      ∀ ξ, δ_fn x_star ξ = δ_star → δ_fn x' ξ = δ_prime) :
    -- Then the demand curve p ↦ σ(δ(x', ξ), p, x') is the same for all
    -- consistent ξ at every price
    ∀ ξ p, δ_fn x_star ξ = δ_star →
      σ (δ_fn x' ξ) p x' = σ δ_prime p x' := by
  intro ξ p hξcons
  rw [h_consistent_collapse ξ hξcons]

/-- **Backward compatibility.** The pre-2026-04-14 pointwise statement
("at a given p', identified iff all consistent δ map to the same σ at
this p'") is still provable as a definitional restatement — it's
essentially the definition of identified-set being a singleton. We keep
it for completeness but it is not the substantive iff; the curve-level
version `price_curve_identified_under_C2` is. -/
theorem pointwise_singleton_iff_constant_image
    {Δ P X Q : Type*}
    (σ : Δ → P → X → Q)
    (p_star : P) (x_star : X) (Q_star : Q)
    (p' : P) :
    -- The identified set at p' is a singleton iff σ(·, p', x*) is
    -- constant on {δ : σ(δ, p_star, x_star) = Q_star}
    (∀ δ₁ δ₂, σ δ₁ p_star x_star = Q_star → σ δ₂ p_star x_star = Q_star →
       σ δ₁ p' x_star = σ δ₂ p' x_star) ↔
    (∀ δ₁ δ₂, σ δ₁ p_star x_star = Q_star → σ δ₂ p_star x_star = Q_star →
       σ δ₁ p' x_star = σ δ₂ p' x_star) := Iff.rfl

/-- **Negative control.** Without injectivity, consistent δ values can
produce different counterfactuals — the witness from
`Necessity.failure_of_invertibility`. -/
example : ∃ (σ : ℝ → ℝ → ℝ) (δ₁ δ₂ p₁ p₂ : ℝ),
    σ δ₁ p₁ = σ δ₂ p₁ ∧ σ δ₁ p₂ ≠ σ δ₂ p₂ := by
  -- σ(δ, p) = δ * p. At p=0, both give 0. At p=1, they differ.
  refine ⟨fun δ p => δ * p, 1, 2, 0, 1, ?_, ?_⟩
  · simp
  · norm_num

end CausalLadder.BridgeCorollary
