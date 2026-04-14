import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith

/-!
# Cross-partial test for separability failure (Proposition `p:cross`)

The paper's separability test: if a demand function `D(p, ξ)` has a nonzero
cross-partial `∂²D/∂p∂ξ`, then it does not satisfy additive separability (AS).

We work scalar-in-`(p, ξ)` for cleanliness; the multi-product version threads
through component-wise without changing the argument.

**Source:** `paper/paper.tex` lines 288–298.
-/

namespace CausalLadder.CrossPartial

/-- **Additive separability (AS) for a scalar demand function.**
A function `D : ℝ → ℝ → ℝ` is AS if it splits as `D p ξ = f p + g ξ`
for some functions `f g : ℝ → ℝ`. -/
def AS (D : ℝ → ℝ → ℝ) : Prop :=
  ∃ f g : ℝ → ℝ, ∀ p ξ, D p ξ = f p + g ξ

/-- **Lemma.** Under AS, the partial derivative `∂D/∂p` evaluated at any
fixed `ξ` equals `f'(p)` — independent of `ξ`. -/
lemma deriv_p_eq_f_deriv
    (D : ℝ → ℝ → ℝ) (f g : ℝ → ℝ)
    (hAS : ∀ p ξ, D p ξ = f p + g ξ)
    (p₀ ξ : ℝ) :
    deriv (fun p => D p ξ) p₀ = deriv f p₀ := by
  have heq : (fun p => D p ξ) = (fun p => f p + g ξ) := funext (fun p => hAS p ξ)
  rw [heq, deriv_add_const]

/-- **Lemma.** Under AS, the function `ξ ↦ ∂D/∂p (p₀, ξ)` is constant. -/
lemma partial_p_constant_in_xi
    (D : ℝ → ℝ → ℝ) (f g : ℝ → ℝ)
    (hAS : ∀ p ξ, D p ξ = f p + g ξ)
    (p₀ : ℝ) :
    (fun ξ => deriv (fun p => D p ξ) p₀) = (fun _ => deriv f p₀) := by
  funext ξ
  exact deriv_p_eq_f_deriv D f g hAS p₀ ξ

/-- **Cross-partial vanishes under AS.** Under AS, the iterated derivative
`∂/∂ξ (∂D/∂p)` is zero everywhere. -/
theorem AS_cross_partial_zero
    (D : ℝ → ℝ → ℝ) (f g : ℝ → ℝ)
    (hAS : ∀ p ξ, D p ξ = f p + g ξ)
    (p₀ ξ₀ : ℝ) :
    deriv (fun ξ => deriv (fun p => D p ξ) p₀) ξ₀ = 0 := by
  rw [partial_p_constant_in_xi D f g hAS p₀, deriv_const]

/-- **Proposition `p:cross` (paper, line 288).** If the cross-partial
`∂²D/∂p∂ξ` is nonzero at some point, then `D` is not additively separable.

Proof by contrapositive of `AS_cross_partial_zero`. -/
theorem cross_partial_test
    (D : ℝ → ℝ → ℝ) (p₀ ξ₀ : ℝ)
    (hne : deriv (fun ξ => deriv (fun p => D p ξ) p₀) ξ₀ ≠ 0) :
    ¬ AS D := by
  rintro ⟨f, g, hAS⟩
  exact hne (AS_cross_partial_zero D f g hAS p₀ ξ₀)

/-- **Equivalent form: dependence of `∂D/∂p` on `ξ` rules out AS.**

This is the form most directly applied in the paper's worked examples
(homogeneous logit, nested logit, CES): one exhibits two `ξ` values
giving different own-price derivatives at the same `p`, which by AS would
be equal. -/
theorem dependence_on_xi_rules_out_AS
    (D : ℝ → ℝ → ℝ) (p₀ ξ₁ ξ₂ : ℝ)
    (hne : deriv (fun p => D p ξ₁) p₀ ≠ deriv (fun p => D p ξ₂) p₀) :
    ¬ AS D := by
  rintro ⟨f, g, hAS⟩
  apply hne
  rw [deriv_p_eq_f_deriv D f g hAS p₀ ξ₁,
      deriv_p_eq_f_deriv D f g hAS p₀ ξ₂]

end CausalLadder.CrossPartial
