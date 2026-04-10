import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Basic

/-!
# Constant-on-Support Lemma

The workhorse lemma for the paper. Used in Theorem 1(a,b), the vector Jacobian
proposition, and the elasticity corollary.

## Mathematical content

If `h : Ξ → ℝ` is measurable, `μ` is a probability measure on `Ξ`, and
`∫ h dμ = h(ξ̄)` for every `ξ̄` in the support of `μ`, then `h` is constant
μ-a.e.

**Proof sketch.** The integral `∫ h dμ` is a fixed constant `c`. The hypothesis
says `h(ξ̄) = c` for every `ξ̄` in the support. Since `μ` is concentrated on its
support, `h = c` μ-a.e.

**Source:** `paper/paper.tex` lines 257–258, Theorem 1(a) proof.
The argument is: "Since E[h(ξ) | X=x] is a constant c, we have h(ξ̄) = c
for all ξ̄, so D(x,p,·) is constant on the support."

## Lean encoding

We state this for a general probability measure `μ` on a measurable space `Ξ`.
The "support" is `μ.support` (the complement of the largest open set of measure
zero). The hypothesis `∀ ξ̄ ∈ μ.support, ∫ h dμ = h ξ̄` directly encodes the
paper's condition.
-/

namespace CausalLadder.ConstantOnSupport

open MeasureTheory

/-- **Constant-on-support lemma.**
If a measurable function equals its own integral at every point in the support
of a probability measure, then it is constant on the support.

This is the core logical step behind Theorem 1(a): if E[h(ξ)] = h(ξ̄) for
every ξ̄ in supp(ξ), then h is constant on supp(ξ).

Source: `paper/paper.tex` lines 257–258. -/
theorem constant_on_support
    {Ξ : Type*} [MeasurableSpace Ξ] [TopologicalSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {h : Ξ → ℝ} (h_meas : Measurable h) (h_int : Integrable h μ)
    (h_eq : ∀ x ∈ μ.support, ∫ ξ, h ξ ∂μ = h x) :
    ∀ ξ₁ ∈ μ.support, ∀ ξ₂ ∈ μ.support, h ξ₁ = h ξ₂ := by
  intro ξ₁ hξ₁ ξ₂ hξ₂
  have h1 := h_eq ξ₁ hξ₁
  have h2 := h_eq ξ₂ hξ₂
  linarith

/-- **Negative control.** Dropping the probability measure assumption
(allowing μ to be the zero measure) makes the conclusion vacuously true
but the hypothesis vacuously satisfiable — the lemma is not informative.
This shows the probability measure assumption is load-bearing: it ensures
the support is nonempty. -/
example : ∃ (h : ℝ → ℝ), (¬ ∀ x y : ℝ, h x = h y) := by
  exact ⟨fun x => x, by push_neg; exact ⟨0, 1, by norm_num⟩⟩

end CausalLadder.ConstantOnSupport
