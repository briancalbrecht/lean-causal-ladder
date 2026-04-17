import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Support
import CausalLadder.ConstantOnSupport

/-!
# ARCHIVED — Vector Analogue of Theorem 1(b) — Jacobian Invariance

**Status: Legacy.** As of commit 928b96d (S2 vector merge, 2026-04-17),
the vector version of Theorem 1 was merged into the main theorem
statement in `paper/paper.tex`. The Appendix A subsection that this file
formalized (formerly lines 617–646) no longer exists.

The content is superseded by:
- `Characterization.lean`: `characterization_b_via_zero_gradient` and
  `vector_additive_decomposition` (added in the same update).

This file is retained for backward compatibility and as a record of the
original entry-wise formalization. No other Lean modules import it.

**Original source:** `paper/paper.tex` lines 617–646 (Appendix A, deleted).
-/

namespace CausalLadder.VectorJacobian

open MeasureTheory CausalLadder.ConstantOnSupport

/-- **Jacobian invariance — each entry is δ-independent.**

If the (j,k)-entry of the Jacobian equals its own integral at every
support point, it is constant on the support. This is the
constant-on-support lemma applied to each matrix entry separately.

Source: `paper/paper.tex` lines 632–634. -/
theorem jacobian_entry_constant
    {Δ : Type*} [MeasurableSpace Δ] [TopologicalSpace Δ]
    {μ : Measure Δ} [IsProbabilityMeasure μ]
    {J : ℕ}
    -- The Jacobian entry (j,k) as a function of δ, parameterized by (p, x)
    {entry : Δ → ℝ}
    (hm : Measurable entry) (hi : Integrable entry μ)
    (h_eq : ∀ δ ∈ μ.support, ∫ δ', entry δ' ∂μ = entry δ) :
    ∀ δ₁ ∈ μ.support, ∀ δ₂ ∈ μ.support, entry δ₁ = entry δ₂ :=
  constant_on_support hm hi h_eq

/-- **Vector additive decomposition.**

If every entry of the Jacobian ∂σ/∂p is δ-independent, then each component
σⱼ decomposes as fⱼ(p) + gⱼ(δ). This is the scalar additive decomposition
applied component-by-component.

We state this for a single component (the paper applies it J times).

Source: `paper/paper.tex` lines 639–643. -/
theorem component_additive_decomposition
    {Δ P : Type*} [Nonempty Δ]
    (σ_j : P → Δ → ℝ)
    (p₀ : P)
    -- The "price-dependent part" σⱼ(p,δ) - σⱼ(p₀,δ) does not depend on δ
    (h_indep : ∀ p δ₁ δ₂, σ_j p δ₁ - σ_j p₀ δ₁ = σ_j p δ₂ - σ_j p₀ δ₂) :
    ∃ (f : P → ℝ) (g : Δ → ℝ), ∀ p δ, σ_j p δ = f p + g δ := by
  obtain ⟨δ₀⟩ := ‹Nonempty Δ›
  refine ⟨fun p => σ_j p δ₀ - σ_j p₀ δ₀, fun δ => σ_j p₀ δ, fun p δ => ?_⟩
  have := h_indep p δ δ₀
  linarith

end CausalLadder.VectorJacobian
