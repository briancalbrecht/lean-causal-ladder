import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

/-!
# Entry Obstruction for Corollary 1(b) — refine item S3 (2026-04-15)

`paper/paper.tex:391` (footnote) and `paper/paper.tex:605-607` (Table 3
rows for *new-product introduction*, *product repositioning*, and *merger
with divestiture*) label each of those counterfactuals as identified
under C1–C3.

The referee's objection: in the standard BLP setting,
`ξ = (ξ₁, …, ξ_J) ∈ ℝ^J` is **product-specific**. Adding product `J+1`
introduces a new component `ξ_{J+1}` that is not in the baseline state
space `ℝ^J`. C3, stated as injectivity of `ξ ↦ δ(x, ξ; θ)` on the
baseline space, cannot recover a component that was never observed.

## What this file proves

`BridgeCorollary.characteristics_curve_identified` (the Lean formal
statement of Corollary 1(b)) uses a **fixed** state-space type `Ξ`. That
theorem is valid under the reading "ξ is a market-level object with a
state space that does not depend on the product set." It is silent about
product-specific ξ under entry.

Under the product-specific reading, any "lift" from `Fin J → ℝ` to
`Fin (J+1) → ℝ` requires choosing the new coordinate. We witness this
concretely at `J = 1`:

- `entry_extensions_not_canonical` — two extensions agreeing on the
  baseline coordinate differ on the new coordinate.
- `entry_demand_not_identified` — a demand system sensitive to the new
  coordinate produces different counterfactual predictions under two
  such extensions. C3 on the baseline space is insufficient.

## What this file does NOT prove

- That the paper's footnote is **wrong** under *any* reading of ξ. Under
  the market-level reading (Ξ fixed across product sets), the existing
  `BridgeCorollary.characteristics_curve_identified` covers entry at the
  cost of an unstated assumption.
- That the obstruction holds for all `J`. The `J = 1` case is proved;
  the general case generalizes straightforwardly but is not needed to
  exhibit the gap.

## Paper-level consequence (for the prose pass)

Table 3's C1–C3 label for new-product introduction / merger with
divestiture is defensible only under an *unstated* market-level-ξ
assumption. The referee's requested fix — narrow to characteristics
changes *within a fixed product set*, or formalize the extra assumption
— is precisely the gap this file exhibits.
-/

namespace CausalLadder.BridgeCorollaryEntry

/-- Product-specific state space at `J = 1`: one real shock. -/
abbrev ΞOne : Type := Fin 1 → ℝ

/-- Product-specific state space at `J = 2`: two real shocks. -/
abbrev ΞTwo : Type := Fin 2 → ℝ

/-- Extension A: preserves the baseline coordinate, sets the new
coordinate to `0`. -/
def extA (v : ΞOne) : ΞTwo := fun i => if i.val = 0 then v 0 else 0

/-- Extension B: preserves the baseline coordinate, sets the new
coordinate to `1`. -/
def extB (v : ΞOne) : ΞTwo := fun i => if i.val = 0 then v 0 else 1

/-- Both extensions preserve the baseline coordinate. -/
theorem extA_preserves (v : ΞOne) : extA v ⟨0, by decide⟩ = v ⟨0, by decide⟩ := by
  simp [extA]

theorem extB_preserves (v : ΞOne) : extB v ⟨0, by decide⟩ = v ⟨0, by decide⟩ := by
  simp [extB]

/-- **Obstruction, version 1: non-canonicity of entry extensions.**

Two entry extensions that both preserve the baseline coordinate disagree
on the new coordinate. C3 on the baseline space recovers a unique
`ξ̄ ∈ ΞOne`, but it does not pin down a unique element of `ΞTwo`: each
value of the new coordinate yields a valid extension. -/
theorem entry_extensions_not_canonical :
    ∃ (v : ΞOne), extA v ≠ extB v := by
  refine ⟨fun _ => 0, ?_⟩
  intro h
  have := congrFun h ⟨1, by decide⟩
  simp [extA, extB] at this

/-- **Obstruction, version 2: entry counterfactual demand is not
identified under C1–C3 with product-specific ξ.**

A baseline market (`J = 1`) has one product and one shock `ξ₀`. C1–C3
pin down `ξ₀` uniquely. The counterfactual (`J+1 = 2` products) has a
demand system sensitive to the new coordinate. Two valid extensions of
the baseline state — both agreeing on `ξ₀` — produce different demands
at the counterfactual. Hence C3 on the baseline is insufficient to
point-identify entry counterfactuals. -/
theorem entry_demand_not_identified :
    ∃ (σ : ΞTwo → ℝ) (v : ΞOne),
      σ (extA v) ≠ σ (extB v) := by
  -- σ depends only on the new coordinate.
  refine ⟨fun w => w ⟨1, by decide⟩, fun _ => 0, ?_⟩
  simp [extA, extB]

/-- **Contrast: under the market-level reading, `BridgeCorollary`
applies.**

If the modeler adopts the convention that `Ξ` is a single fixed type
(market-level ξ) across product-set changes, then `δ : X → Ξ → Δ` is
well-defined at the counterfactual `x'` regardless of whether `x'`
involves more products than `x*`. In that case
`BridgeCorollary.characteristics_curve_identified` directly applies.

This is the assumption the paper's Table 3 implicitly relies on but does
not state. The referee's fix is to make it explicit or to narrow the
table to characteristics changes within a fixed product set. -/
theorem market_level_xi_recovers_entry
    {Δ P X Q Ξ_fixed : Type*}
    (σ : Δ → P → X → Q)
    (δ_fn : X → Ξ_fixed → Δ)
    (x_star x_entry : X) (δ_star : Δ)
    (δ_prime : Δ)
    (h_consistent_collapse :
      ∀ ξ, δ_fn x_star ξ = δ_star → δ_fn x_entry ξ = δ_prime) :
    ∀ ξ p, δ_fn x_star ξ = δ_star →
      σ (δ_fn x_entry ξ) p x_entry = σ δ_prime p x_entry := by
  intro ξ p hξcons
  rw [h_consistent_collapse ξ hξcons]

end CausalLadder.BridgeCorollaryEntry
