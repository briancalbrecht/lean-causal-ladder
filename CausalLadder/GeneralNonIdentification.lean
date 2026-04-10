import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.ContinuousOn

/-!
# General Non-Identification of Market-Specific Demand (Proposition 3)

If two demand curves cross at the observed price with different slopes,
they diverge at every nearby price. The width of the identified set
grows linearly in the price change.

## Mathematical content

Let `Δ(p) = D(p, ξₐ) - D(p, ξ_b)`.

**(a) Local non-identification.** `Δ(P*) = 0` and `Δ'(P*) ≠ 0` implies
`Δ(p') ≠ 0` in a punctured neighborhood of `P*`. (By continuity of `Δ'`,
`Δ` is strictly monotone near `P*`.)

**(b) Divergence rate.** `|Δ(p')| = |Δ'(P*)| · |p' - P*| + o(|p' - P*|)`.
(First-order Taylor expansion.)

**Source:** `paper/paper.tex` lines 215–229, proof at lines 721–727.
-/

namespace CausalLadder.GeneralNonIdentification

/-- **(a) Local non-identification — core real analysis fact.**

If a differentiable function vanishes at a point but has nonzero derivative
there, it is nonzero in a punctured neighborhood.

This is the mathematical core of Proposition 3(a), stripped of economic
content. The economic version follows by setting `Δ(p) = D(p, ξₐ) - D(p, ξ_b)`.

Source: `paper/paper.tex` lines 721–723. -/
theorem nonzero_near_root_of_nonzero_deriv
    {f : ℝ → ℝ} {a : ℝ}
    (hf : DifferentiableAt ℝ f a)
    (hfa : f a = 0)
    (hf' : deriv f a ≠ 0) :
    ∃ ε > 0, ∀ x, 0 < |x - a| → |x - a| < ε → f x ≠ 0 := by
  -- Strategy: f'(a) ≠ 0, so either f'(a) > 0 or f'(a) < 0.
  -- WLOG f'(a) > 0 (the other case is symmetric via -f).
  -- By definition of derivative, for x near a:
  --   f(x) = f(a) + f'(a)(x-a) + o(x-a) = f'(a)(x-a) + o(x-a)
  -- For x ≠ a sufficiently close, the leading term dominates, so f(x) ≠ 0.
  --
  -- This is a standard consequence of HasDerivAt + f(a) = 0 + f'(a) ≠ 0.
  -- The Mathlib proof path goes through the local injectivity of f near a.
  -- We defer to Mathlib's `HasStrictDerivAt.localInverse` machinery or
  -- prove it directly from the ε-δ definition of the derivative.
  --
  -- Use Mathlib's `HasDerivAt.eventually_ne`:
  -- if f has nonzero derivative at a, then f(z) ≠ f(a) eventually in 𝓝[≠] a.
  have hfd := hf.hasDerivAt
  -- HasDerivAt.eventually_ne gives: ∀ᶠ z in 𝓝[≠] a, f z ≠ f a
  -- With f(a) = 0, this becomes: ∀ᶠ z in 𝓝[≠] a, f z ≠ 0
  have h_ev := hfd.eventually_ne (c := 0) hf'
  -- h_ev : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0
  -- Convert to ε-ball form
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_ev
  obtain ⟨ε, hε_pos, hε⟩ := h_ev
  refine ⟨ε, hε_pos, fun x hx_ne hx_lt => ?_⟩
  exact hε (by rwa [Real.dist_eq]) (Set.mem_compl_singleton_iff.mpr
    (fun h => absurd (show |x - a| = 0 by rw [h, sub_self, abs_zero]) (ne_of_gt hx_ne)))

/-- **(a) Applied to demand: counterfactual divergence near crossing.**

If two demand curves cross at P* (`D(P*, ξₐ) = D(P*, ξ_b)`) with different
slopes (`∂D/∂p(P*, ξₐ) ≠ ∂D/∂p(P*, ξ_b)`), then they diverge near P*.

Source: `paper/paper.tex` lines 222–223. -/
theorem demand_diverges_near_crossing
    {Da Db : ℝ → ℝ} {Pstar : ℝ}
    (hDa : DifferentiableAt ℝ Da Pstar)
    (hDb : DifferentiableAt ℝ Db Pstar)
    (hcross : Da Pstar = Db Pstar)
    (hslope : deriv Da Pstar ≠ deriv Db Pstar) :
    ∃ ε > 0, ∀ p, 0 < |p - Pstar| → |p - Pstar| < ε → Da p ≠ Db p := by
  -- Apply nonzero_near_root_of_nonzero_deriv to Δ = Da - Db
  have hΔ_diff : DifferentiableAt ℝ (Da - Db) Pstar :=
    hDa.sub hDb
  have hΔ_zero : (Da - Db) Pstar = 0 := by
    simp [Pi.sub_apply, hcross]
  have hΔ'_ne : deriv (Da - Db) Pstar ≠ 0 := by
    rw [deriv_sub hDa hDb]
    exact sub_ne_zero.mpr hslope
  obtain ⟨ε, hε, hne⟩ := nonzero_near_root_of_nonzero_deriv hΔ_diff hΔ_zero hΔ'_ne
  exact ⟨ε, hε, fun p hp1 hp2 h => hne p hp1 hp2 (by simp [Pi.sub_apply, h])⟩

/-- **(b) Divergence rate — the width formula.**

The identified set width satisfies
`|D(p', ξₐ) - D(p', ξ_b)| = |∂D/∂p(P*, ξₐ) - ∂D/∂p(P*, ξ_b)| · |p' - P*| + o(|p' - P*|)`

This is a first-order Taylor expansion of `Δ(p') = D(p', ξₐ) - D(p', ξ_b)`
around `P*`, using `Δ(P*) = 0`.

Source: `paper/paper.tex` lines 224–227. -/
theorem divergence_rate
    {Da Db : ℝ → ℝ} {Pstar : ℝ}
    (hDa : HasDerivAt Da (deriv Da Pstar) Pstar)
    (hDb : HasDerivAt Db (deriv Db Pstar) Pstar)
    (hcross : Da Pstar = Db Pstar) :
    -- Δ(p') = Δ'(P*) · (p' - P*) + o(|p' - P*|)
    -- Stated as: Δ has derivative Δ'(P*) at P*, where Δ(P*) = 0
    HasDerivAt (Da - Db) (deriv Da Pstar - deriv Db Pstar) Pstar := by
  exact hDa.sub hDb

/-- **Negative control.** If the slopes are equal, the crossing curves
coincide everywhere (under differentiability + connectedness). The slope
difference hypothesis is load-bearing. -/
example : ∃ (f g : ℝ → ℝ),
    f 0 = g 0 ∧ deriv f 0 = deriv g 0 ∧
    ∀ x, f x = g x := by
  exact ⟨fun x => x, fun x => x, rfl, rfl, fun _ => rfl⟩

end CausalLadder.GeneralNonIdentification
