import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Nested logit own-price derivative — masking analysis (Appendix A)

Two formulas for the nested-logit own-price derivative differ by a transposition
of the coefficients on the within-nest share `σ_{j|g}` and the unconditional
share `σ_j`:

  wrong: `-(α/λ) σ_j (1 - λ      σ_{j|g} - (1-λ) σ_j)`
  right: `-(α/λ) σ_j (1 - (1-λ)  σ_{j|g} -  λ    σ_j)`

The wrong formula appeared in `paper/paper.tex` line 716 from
2026-03-24 (commit 7447853, Phase 12D) until 2026-04-14 (commit 2cb8487).

This file does *not* re-derive either formula from `Real.exp`; that lives in
`tests/math-tests.wls`. Instead it formalises the **masking identity**
that explains how the bug evaded detection for three weeks:

  wrong − right = -(α/λ) · σ_j · (1 − 2λ) · (σ_{j|g} − σ_j)

So the two formulas agree exactly when:
  • `λ = 1/2`, or
  • `σ_{j|g} = σ_j`, or
  • `σ_j = 0`.

Any spot check done at `λ = 1/2` — the symmetric nesting parameter, and also
the unique value at which the (independently buggy) IV exponent makes shares
sum to 1 — would pass under *both* formulas. That is the gap the regression
tests in `tests/math-tests.wls` now close.

**Source:** `paper/paper.tex` line 716; commit `2cb8487` (2026-04-14).
-/

namespace CausalLadder.NestedLogit

/-- Buggy own-price derivative formula (paper line 716, commits 7447853..2cb8487~1). -/
noncomputable def wrongFormula (α lam σ_jg σ_j : ℝ) : ℝ :=
  -(α / lam) * σ_j * (1 - lam * σ_jg - (1 - lam) * σ_j)

/-- Corrected own-price derivative formula (commit 2cb8487 onward). -/
noncomputable def rightFormula (α lam σ_jg σ_j : ℝ) : ℝ :=
  -(α / lam) * σ_j * (1 - (1 - lam) * σ_jg - lam * σ_j)

/-- **Masking identity.** The two formulas differ by a single product:
the masking factor `(1 − 2λ)(σ_{j|g} − σ_j)`, scaled by `-(α/λ) σ_j`.

This is the structural reason why specific spot checks could not detect the bug. -/
theorem wrong_minus_right (α lam σ_jg σ_j : ℝ) :
    wrongFormula α lam σ_jg σ_j - rightFormula α lam σ_jg σ_j
      = -(α / lam) * σ_j * (1 - 2 * lam) * (σ_jg - σ_j) := by
  unfold wrongFormula rightFormula
  ring

/-- **Masking case 1: λ = 1/2.** At the symmetric nesting parameter, both
formulas give the same value — for *any* shares. This is the same value of
λ at which the (independently buggy) IV-exponent formula happens to make
shares sum to 1, so any sanity check pinned to `λ = 1/2` would pass under
both errors simultaneously. -/
theorem agree_at_half (α σ_jg σ_j : ℝ) :
    wrongFormula α (1/2) σ_jg σ_j = rightFormula α (1/2) σ_jg σ_j := by
  unfold wrongFormula rightFormula
  ring

/-- **Masking case 2: symmetric within-nest shares.** When `σ_{j|g} = σ_j`
(e.g. a single-product nest, where the within-nest share is 1 and the
unconditional share is the nest share — degenerate but a common test case),
both formulas agree for *any* λ. -/
theorem agree_at_symmetric (α lam σ : ℝ) :
    wrongFormula α lam σ σ = rightFormula α lam σ σ := by
  unfold wrongFormula rightFormula
  ring

/-- **Masking case 3: degenerate share.** If `σ_j = 0`, both formulas vanish.
The bug is invisible when the product has zero predicted share. -/
theorem agree_at_zero_share (α lam σ_jg : ℝ) :
    wrongFormula α lam σ_jg 0 = rightFormula α lam σ_jg 0 := by
  unfold wrongFormula rightFormula
  ring

/-- **Off-critical disagreement.** A concrete numerical witness:
at `α = 1, λ = 1/3, σ_{j|g} = 1/2, σ_j = 1/4`, the formulas differ.
This is the smallest reasonable perturbation away from `λ = 1/2` and
`σ_{j|g} = σ_j` — exactly the kind of value the missing regression test
needed to use. -/
theorem disagree_off_critical :
    wrongFormula 1 (1/3) (1/2) (1/4) ≠ rightFormula 1 (1/3) (1/2) (1/4) := by
  unfold wrongFormula rightFormula
  norm_num

/-- **Necessary and sufficient condition for the bug to hide.**
Assuming nondegenerate parameters (`α ≠ 0`, `λ ≠ 0`, `σ_j ≠ 0`),
the wrong formula equals the right formula **if and only if**
`λ = 1/2` or `σ_{j|g} = σ_j`.

This pinpoints what a *cheap* sanity check would have missed: any quick
hand-substitution at the canonical symmetric value `λ = 1/2`, or at a
single-product nest where `σ_{j|g} = σ_j`, would have agreed with the
truth. The actual test gap was wider — commit `2cb8487` records that
`tests/math-tests.wls` had **zero** nested-logit coverage when the wrong
formula was committed in `7447853`. The fix adds a numerical regression
at `λ = 3/10` (off-critical), which catches the bug. -/
theorem mask_iff
    (α lam σ_jg σ_j : ℝ)
    (hα : α ≠ 0) (hlam : lam ≠ 0) (hσj : σ_j ≠ 0) :
    wrongFormula α lam σ_jg σ_j = rightFormula α lam σ_jg σ_j
      ↔ lam = 1/2 ∨ σ_jg = σ_j := by
  -- The two formulas agree iff their difference is zero.
  rw [← sub_eq_zero, wrong_minus_right]
  -- The difference factors as `-(α/λ) σ_j · (1 − 2λ) · (σ_{j|g} − σ_j)`,
  -- so under nondegeneracy it vanishes iff one of the last two factors does.
  have hcoef : -(α / lam) * σ_j ≠ 0 := by
    have hαlam : α / lam ≠ 0 := div_ne_zero hα hlam
    have : -(α / lam) ≠ 0 := neg_ne_zero.mpr hαlam
    exact mul_ne_zero this hσj
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h11 | h12
      · exact absurd h11 hcoef
      · left; linarith
    · right; linarith
  · rintro (hlam' | hσ)
    · have h1 : (1 - 2 * lam) = 0 := by rw [hlam']; ring
      rw [show -(α / lam) * σ_j * (1 - 2 * lam) * (σ_jg - σ_j)
            = (-(α / lam) * σ_j) * ((1 - 2 * lam) * (σ_jg - σ_j)) by ring,
          h1]
      ring
    · have h2 : (σ_jg - σ_j) = 0 := by rw [hσ]; ring
      rw [show -(α / lam) * σ_j * (1 - 2 * lam) * (σ_jg - σ_j)
            = (-(α / lam) * σ_j * (1 - 2 * lam)) * (σ_jg - σ_j) by ring,
          h2]
      ring

end CausalLadder.NestedLogit
