import CausalLadder.Characterization
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Reduced-form informativeness (Corollary `c:rf`)

The paper's reduced-form corollary: the average derivative `∂m/∂p`
identifiable from experiments or instruments equals every market's demand
slope **iff** AS holds.

This is a re-packaging of Theorem 1(b) (`slopes_forward_core` in
`Characterization.lean`) for the object that reduced-form work actually
identifies — the average derivative — rather than the level `m` itself.

We split the iff into two directions, each stated under the cleanest
sufficient hypothesis:

* `avg_derivative_eq_every_slope_implies_xi_free` (⇒): identical content to
  `slopes_forward_core`, restated for the reduced-form object.
* `xi_free_slope_eq_avg_derivative` (⇐): if the slope is globally `ξ`-free,
  the integral against any probability measure recovers it.

**Source:** `paper/paper.tex` lines 837–842.
-/

namespace CausalLadder.ReducedForm

open MeasureTheory

variable {Ξ : Type*} [MeasurableSpace Ξ] [TopologicalSpace Ξ]

/-- **Forward (`⇒`).** If the experimental average derivative
`∂m/∂p (p) = ∫ ∂D/∂p (p, ξ') dμ(ξ')` equals every market's slope
`∂D/∂p (p, ξ)` at every support point, then `∂D/∂p` is `ξ`-free on the
support — the headline ingredient of (AS).

This is `Characterization.slopes_forward_core` re-stated for the
average-derivative object the reduced-form analyst actually has access to.

Source: `paper/paper.tex` line 838. -/
theorem avg_derivative_eq_every_slope_implies_xi_free
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {dDdp : ℝ → Ξ → ℝ}
    (hm : ∀ p, Measurable (dDdp p))
    (hi : ∀ p, Integrable (dDdp p) μ)
    (h_eq : ∀ p, ∀ ξ ∈ μ.support, ∫ ξ', dDdp p ξ' ∂μ = dDdp p ξ) :
    ∀ p, ∀ ξ₁ ∈ μ.support, ∀ ξ₂ ∈ μ.support, dDdp p ξ₁ = dDdp p ξ₂ :=
  CausalLadder.Characterization.slopes_forward_core hm hi h_eq

/-- **Backward (`⇐`).** If the slope is globally `ξ`-free
(there exists `φ : ℝ → ℝ` with `∂D/∂p (p, ξ) = φ(p)` for every `ξ`), then
the experimental average derivative equals `φ(p)`, which equals every
market's slope.

We state the strong form (globally constant in `ξ`) rather than
"constant on the support" because the latter requires the measure-theoretic
fact that `μ.support` has full measure under the relevant topological
hypotheses; the strong form needs no such side condition and is the form
delivered by AS in any case.

Source: `paper/paper.tex` line 839. -/
theorem xi_free_slope_eq_avg_derivative
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (dDdp : ℝ → Ξ → ℝ) (φ : ℝ → ℝ)
    (h_const : ∀ p ξ, dDdp p ξ = φ p) :
    ∀ p ξ, ∫ ξ', dDdp p ξ' ∂μ = dDdp p ξ := by
  intro p ξ
  have h1 : (fun ξ' => dDdp p ξ') = (fun _ => φ p) := by
    funext ξ'; exact h_const p ξ'
  have h2 : ∫ _ : Ξ, φ p ∂μ = φ p := by
    rw [integral_const, measureReal_univ_eq_one, one_smul]
  calc ∫ ξ', dDdp p ξ' ∂μ
      = ∫ _ : Ξ, φ p ∂μ := by rw [h1]
    _ = φ p := h2
    _ = dDdp p ξ := (h_const p ξ).symm

end CausalLadder.ReducedForm
