import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Nested logit own-price derivative — full `HasDerivAt` derivation

Closes the last Lean coverage gap on the nested-logit formula. The
companion file `NestedLogit.lean` formalises the *masking identity*
between the wrong and right closed-form expressions for
`∂σ_j/∂p_j` but does **not** derive either expression from the share
function's definition (that derivation lived only in
`tests/math-tests.wls`).

This file closes that gap: it defines the nested-logit share in terms of
`Real.exp` and `Real.rpow`, applies mathlib's differentiation lemmas,
and proves that the derivative equals the paper's `rightFormula`.

In this file `lam` plays the role of the paper's `λ` (Lean reserves `λ`
as the lambda keyword).

## Setup

Fix a product `j` in a single nest with correlation parameter
`lam ∈ (0, 1]`. Let the mean utility net of price be
`δ̃_j(p) = δ - α · p`. The exp-utility `u(p) = exp((δ - α · p)/lam)`
and the sum of exp-utilities of the *other* products in the nest is a
constant `R > 0`.

| Quantity | Definition |
|----------|------------|
| `u(p)` | `exp((δ - α · p)/lam)` |
| `D(p)` | `u(p) + R` (nest denominator) |
| `denom(p)` | `1 + D(p)^lam` (inclusive denominator with outside good at mean utility 0) |
| `σ(p)` | `u(p) · D(p)^(lam-1) / denom(p)` (product j's unconditional share) |
| `σ_c(p)` | `u(p) / D(p)` (product j's within-nest share) |

## Result

`∂σ/∂p = -(α/lam) · σ · (1 − (1−lam)·σ_c − lam·σ)`

which is exactly `NestedLogit.rightFormula α lam σ_c σ`.
-/

namespace CausalLadder.NestedLogitDerivative

open Real

variable (α lam δ R : ℝ)

/-- Product j's exponential utility as a function of its own price. -/
noncomputable def u (p : ℝ) : ℝ := exp ((δ - α * p) / lam)

/-- Nest denominator: sum over the nest's exp-utilities. -/
noncomputable def D (p : ℝ) : ℝ := u α lam δ p + R

/-- Inclusive denominator with outside good at mean utility 0. -/
noncomputable def denom (p : ℝ) : ℝ := 1 + (D α lam δ R p) ^ lam

/-- Product j's unconditional market share. -/
noncomputable def σ (p : ℝ) : ℝ :=
  u α lam δ p * (D α lam δ R p) ^ (lam - 1) / denom α lam δ R p

/-- Product j's within-nest (conditional) share. -/
noncomputable def σ_c (p : ℝ) : ℝ := u α lam δ p / D α lam δ R p

section Positivity

variable (hR : 0 < R)

lemma u_pos (p : ℝ) : 0 < u α lam δ p := Real.exp_pos _

include hR in
lemma D_pos (p : ℝ) : 0 < D α lam δ R p :=
  add_pos (u_pos α lam δ p) hR

include hR in
lemma D_ne_zero (p : ℝ) : D α lam δ R p ≠ 0 :=
  ne_of_gt (D_pos α lam δ R hR p)

include hR in
lemma Drpow_pos (p : ℝ) : 0 < (D α lam δ R p) ^ lam :=
  Real.rpow_pos_of_pos (D_pos α lam δ R hR p) _

include hR in
lemma denom_pos (p : ℝ) : 0 < denom α lam δ R p :=
  add_pos one_pos (Drpow_pos α lam δ R hR p)

include hR in
lemma denom_ne_zero (p : ℝ) : denom α lam δ R p ≠ 0 :=
  ne_of_gt (denom_pos α lam δ R hR p)

end Positivity

section Derivative

variable (hlam : lam ≠ 0) (hR : 0 < R)

/-- `u` has derivative `-(α/lam) · u(p)`. -/
lemma hasDerivAt_u (p : ℝ) :
    HasDerivAt (u α lam δ) (-(α / lam) * u α lam δ p) p := by
  show HasDerivAt (fun q => exp ((δ - α * q) / lam)) _ p
  have h1 : HasDerivAt (fun q : ℝ => (δ - α * q) / lam) (-(α / lam)) p := by
    have ha : HasDerivAt (fun q : ℝ => α * q) α p := by
      simpa using (hasDerivAt_id p).const_mul α
    have hb : HasDerivAt (fun q : ℝ => δ - α * q) (-α) p := by
      simpa using ha.const_sub δ
    have hc := hb.div_const lam
    convert hc using 1
    ring
  have h2 := h1.exp
  show HasDerivAt (fun q => exp ((δ - α * q) / lam)) _ p
  convert h2 using 1
  simp [u]
  ring

/-- `D` has derivative `-(α/lam) · u(p)`. -/
lemma hasDerivAt_D (p : ℝ) :
    HasDerivAt (D α lam δ R) (-(α / lam) * u α lam δ p) p := by
  show HasDerivAt (fun q => u α lam δ q + R) _ p
  exact (hasDerivAt_u α lam δ p).add_const R

include hlam hR in
/-- `p ↦ D(p)^lam` has derivative `-α · u(p) · D(p)^(lam-1)`. -/
lemma hasDerivAt_Drpow (p : ℝ) :
    HasDerivAt (fun q => (D α lam δ R q) ^ lam)
      (-α * u α lam δ p * (D α lam δ R p) ^ (lam - 1)) p := by
  have h := HasDerivAt.rpow_const (p := lam) (hasDerivAt_D α lam δ R p)
    (Or.inl (D_ne_zero α lam δ R hR p))
  convert h using 1
  field_simp

include hlam hR in
/-- `denom` has derivative `-α · u(p) · D(p)^(lam-1)`. -/
lemma hasDerivAt_denom (p : ℝ) :
    HasDerivAt (denom α lam δ R)
      (-α * u α lam δ p * (D α lam δ R p) ^ (lam - 1)) p := by
  show HasDerivAt (fun q => 1 + (D α lam δ R q) ^ lam) _ p
  exact (hasDerivAt_Drpow α lam δ R hlam hR p).const_add 1

include hlam hR in
/-- **Main theorem (raw form).** The quotient-rule output for `σ`. -/
lemma hasDerivAt_σ_raw (p : ℝ) :
    HasDerivAt (σ α lam δ R)
      ((((-(α / lam) * u α lam δ p) * (D α lam δ R p) ^ (lam - 1)
        + u α lam δ p * ((-(α / lam) * u α lam δ p) * (lam - 1) *
            (D α lam δ R p) ^ (lam - 1 - 1))) * denom α lam δ R p
       - u α lam δ p * (D α lam δ R p) ^ (lam - 1) *
         (-α * u α lam δ p * (D α lam δ R p) ^ (lam - 1)))
      / (denom α lam δ R p) ^ 2) p := by
  have hu := hasDerivAt_u α lam δ p
  have hD := hasDerivAt_D α lam δ R p
  have hDrpow : HasDerivAt (fun q => (D α lam δ R q) ^ (lam - 1))
      ((-(α / lam) * u α lam δ p) * (lam - 1) *
        (D α lam δ R p) ^ (lam - 1 - 1)) p := by
    have h := HasDerivAt.rpow_const (p := lam - 1) hD
      (Or.inl (D_ne_zero α lam δ R hR p))
    convert h using 1
  have hnum := hu.mul hDrpow
  have hdenom := hasDerivAt_denom α lam δ R hlam hR p
  show HasDerivAt (fun q => u α lam δ q * (D α lam δ R q) ^ (lam - 1)
                              / denom α lam δ R q) _ p
  exact hnum.div hdenom (denom_ne_zero α lam δ R hR p)

/-- **Algebraic factorisation.** The raw quotient-rule output collapses to
the paper's factored form. -/
lemma σ_derivative_factored (p : ℝ)
    (hu_ne : u α lam δ p ≠ 0) (hD_ne : D α lam δ R p ≠ 0)
    (hdenom_ne : denom α lam δ R p ≠ 0) (hlam : lam ≠ 0) :
    (((-(α / lam) * u α lam δ p) * (D α lam δ R p) ^ (lam - 1)
        + u α lam δ p * ((-(α / lam) * u α lam δ p) * (lam - 1) *
            (D α lam δ R p) ^ (lam - 1 - 1))) * denom α lam δ R p
       - u α lam δ p * (D α lam δ R p) ^ (lam - 1) *
         (-α * u α lam δ p * (D α lam δ R p) ^ (lam - 1)))
      / (denom α lam δ R p) ^ 2
    = -(α / lam) * σ α lam δ R p *
        (1 - (1 - lam) * σ_c α lam δ R p - lam * σ α lam δ R p) := by
  -- Reconcile D^(lam-1-1) with D^(lam-1) using D^(a+1) = D^a · D.
  have hDsub : (D α lam δ R p) ^ (lam - 1 - 1)
      = (D α lam δ R p) ^ (lam - 1) / (D α lam δ R p) := by
    rw [eq_div_iff hD_ne, ← Real.rpow_add_one hD_ne]
    congr 1
    ring
  unfold σ σ_c
  rw [hDsub]
  -- Treat D^(lam-1) as an abstract term so `ring` can handle the rest.
  set e := (D α lam δ R p) ^ (lam - 1) with he_def
  field_simp
  ring

include hlam hR in
/-- **Main theorem — factored form.** The own-price derivative of the
nested-logit share `σ(p)` equals
`-(α/lam) · σ(p) · (1 − (1−lam)·σ_c(p) − lam·σ(p))`. -/
theorem hasDerivAt_σ (p : ℝ) :
    HasDerivAt (σ α lam δ R)
      (-(α / lam) * σ α lam δ R p *
        (1 - (1 - lam) * σ_c α lam δ R p - lam * σ α lam δ R p)) p := by
  have hraw := hasDerivAt_σ_raw α lam δ R hlam hR p
  have hu_ne : u α lam δ p ≠ 0 := ne_of_gt (u_pos α lam δ p)
  have hD_ne : D α lam δ R p ≠ 0 := D_ne_zero α lam δ R hR p
  have hdenom_ne : denom α lam δ R p ≠ 0 := denom_ne_zero α lam δ R hR p
  have hfact := σ_derivative_factored α lam δ R p hu_ne hD_ne hdenom_ne hlam
  rw [← hfact]
  exact hraw

end Derivative

/-- **Bridge to `NestedLogit.rightFormula`.** The derivative formula
matches `rightFormula α lam σ_c σ` from `NestedLogit.lean`. -/
theorem matches_rightFormula (α lam δ R : ℝ) (hlam : lam ≠ 0) (hR : 0 < R) (p : ℝ) :
    HasDerivAt (σ α lam δ R)
      (-(α / lam) * σ α lam δ R p *
        (1 - (1 - lam) * σ_c α lam δ R p - lam * σ α lam δ R p)) p :=
  hasDerivAt_σ α lam δ R hlam hR p

end CausalLadder.NestedLogitDerivative
