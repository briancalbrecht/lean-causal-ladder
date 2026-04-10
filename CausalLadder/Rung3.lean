import Mathlib.Data.Real.Basic

/-!
# The Demand Curve is a Rung 3 Object (Proposition 1, §6)

The ceteris paribus demand curve is a unit-level counterfactual: it depends on
the specific market's realized conditions. The experimental average integrates
over those conditions and is therefore a population-level (Rung 2) object.

## Mathematical content

Given structural equations:
- `X = g_X(u_X)`, `ξ = g_ξ(u_ξ)` (exogenous variables determined by unit `u`)
- `Q_p(u) = D(g_X(u_X), p, g_ξ(u_ξ))` (counterfactual demand at price `p`)

Fixing `u` fixes `(x̄, ξ̄)`, so `p ↦ Q_p(u)` is `q_{x̄,ξ̄}(p)` from Definition 1.
Since `Q_p(u)` depends on the unit `u`, it is a Rung 3 (unit-level) quantity.
The experimental average `m(p,x) = E[Q_p(u) | X=x]` integrates over `u`
and is therefore Rung 2 (population-level).

The proof is purely definitional: compose the structural equations and observe
that the result matches Definition 1.

**Source:** `paper/paper.tex` lines 480–485.
-/

namespace CausalLadder.Rung3

/-- **The demand curve is a unit-level counterfactual.**

Given structural equations mapping unit `u` to observables, the counterfactual
demand `Q_p(u) = D(g_X(u_X), p, g_ξ(u_ξ))` at a fixed unit `u` coincides with
the market-specific demand curve `q(p) = D(x̄, p, ξ̄)` where `x̄ = g_X(u_X)`
and `ξ̄ = g_ξ(u_ξ)`.

This is the formal content of "the demand curve is Rung 3": it depends on
the specific unit `u`, not just population averages.

Source: `paper/paper.tex` lines 483–484. -/
theorem demand_curve_is_unit_level
    {U_X U_ξ X Ξ P Q : Type*}
    -- Structural equations
    (g_X : U_X → X) (g_ξ : U_ξ → Ξ)
    -- Demand function
    (D : X → P → Ξ → Q)
    -- A specific unit
    (u_X : U_X) (u_ξ : U_ξ)
    -- The realized characteristics
    (x_bar : X) (hx : x_bar = g_X u_X)
    (ξ_bar : Ξ) (hξ : ξ_bar = g_ξ u_ξ)
    -- Any counterfactual price
    (p : P) :
    -- The counterfactual Q_p(u) = D(g_X(u_X), p, g_ξ(u_ξ)) equals
    -- the market-specific demand curve q_{x̄,ξ̄}(p) = D(x̄, p, ξ̄)
    D (g_X u_X) p (g_ξ u_ξ) = D x_bar p ξ_bar := by
  rw [hx, hξ]

/-- **Negative control.** Two different units with different ξ values
produce different counterfactual demands (in general). This shows the
dependence on `u` is real — the demand curve is genuinely unit-level,
not a population object. -/
example : ∃ (D : ℝ → ℝ → ℝ) (ξ₁ ξ₂ p : ℝ),
    ξ₁ ≠ ξ₂ ∧ D p ξ₁ ≠ D p ξ₂ := by
  -- D(p, ξ) = p + ξ. Different ξ gives different demand.
  exact ⟨fun p ξ => p + ξ, 0, 1, 0, by norm_num, by norm_num⟩

end CausalLadder.Rung3
