import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Support
import CausalLadder.ConstantOnSupport

/-!
# Elasticity Version of the Gap (Corollary 2)

Even under additive separability, population-average elasticities differ from
unit-level elasticities because the demand *level* varies with ξ.

## Mathematical content

The own-price elasticity `η(x,p,ξ) = (p/D(x,p,ξ)) · ∂D/∂p(x,p,ξ)` depends
on ξ through the demand level D(x,p,ξ), even when ∂D/∂p is ξ-free.

`E[η] = η(ξ̄)` for all ξ̄ iff η does not depend on ξ. This is the same
constant-on-support argument as Theorem 1(a), applied to η instead of D.

**Source:** `paper/paper.tex` lines 758–768 (Appendix C).
-/

namespace CausalLadder.ElasticityGap

open MeasureTheory CausalLadder.ConstantOnSupport

/-- **Corollary 2: Elasticity gap — forward direction.**

If the population-average elasticity equals every market's elasticity,
then the elasticity is constant in ξ. Same logic as Theorem 1(a).

Source: `paper/paper.tex` lines 766–768. -/
theorem elasticity_constant_on_support
    {Ξ : Type*} [MeasurableSpace Ξ] [TopologicalSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {η : Ξ → ℝ}
    (hm : Measurable η) (hi : Integrable η μ)
    (h_eq : ∀ ξ ∈ μ.support, ∫ ξ', η ξ' ∂μ = η ξ) :
    ∀ ξ₁ ∈ μ.support, ∀ ξ₂ ∈ μ.support, η ξ₁ = η ξ₂ :=
  constant_on_support hm hi h_eq

/-- **Elasticity gap exists under additive separability.**

Under (AS), `D(p, ξ) = f(p) + g(ξ)` and `∂D/∂p = f'(p)`. The elasticity is
`η(p, ξ) = p · f'(p) / (f(p) + g(ξ))`. Unless `g` is constant, η varies
with ξ through the denominator.

Concrete witness: `f(p) = -p`, `g(ξ) = ξ`, so `D = ξ - p` and
`η = p / (ξ - p)`. At p=1: η(ξ=3) = 1/2, η(ξ=5) = 1/4. -/
theorem elasticity_varies_under_AS :
    let η := fun (ξ : ℝ) => (1 : ℝ) / (ξ - 1)
    η 3 ≠ η 5 := by
  simp only
  norm_num

end CausalLadder.ElasticityGap
