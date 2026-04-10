# Lean Formalization: Abduction and the Demand Curve

Formal verification of the main results in "Abduction and the Demand Curve" by Brian C. Albrecht and James Traina.

## Main results

The paper proves that Berry inversion is **necessary and sufficient** for recovering market-specific counterfactuals from demand data. Prior work (Berry 1994, Berry-Haile 2014, 2021) established sufficiency only.

## Coverage table

| Paper Claim | Label | Lean File | Theorem | Status |
|---|---|---|---|---|
| Prop 1: Constructive gap | `p:gap` | `ConstructiveGap.lean` | `observational_equivalence`, `counterfactual_divergence` | ✅ |
| Prop 3: General non-identification | `p:general` | `GeneralNonIdentification.lean` | — | 🔧 TODO |
| Thm 1: AS iff gap vanishes | `t:char` | `Characterization.lean` | — | 🔧 TODO |
| Thm 2: Structural model identifies | `t:bridge` | `BridgeTheorem.lean` | `price_counterfactual_recovery`, `characteristics_counterfactual_recovery` | ✅ |
| Prop 4: Necessity of C2/C3 | `p:necessity` | `Necessity.lean` | `failure_of_invertibility`, `failure_of_recoverability` | ✅ |
| Cor 1: Inversion iff point-id | `c:bridge` | `BridgeCorollary.lean` | `price_counterfactual_iff_invertibility` | ✅ |
| Prop (§6): Demand is Rung 3 | `p:rung3` | `Rung3.lean` | — | 🔧 TODO |
| Prop: Vector Jacobian | `p:jacobian` | `VectorJacobian.lean` | — | 🔧 TODO |
| Cor 2: Elasticity gap | `c:elas` | `ElasticityGap.lean` | — | 🔧 TODO |
| Core lemma | — | `ConstantOnSupport.lean` | `constant_on_support` | ✅ |

**Not formalized:**
- Proposition `p:express` (expressiveness boundary) — requires formalizing causal graphs and do-calculus completeness, which is outside Mathlib
- Remark `r:estimation` (estimation uncertainty) — invokes GMM asymptotics
- Remark `r:partial` (partial identification) — discursive, no new formal content

## Architecture

```
CausalLadder/
├── ConstantOnSupport.lean       # Core lemma: E[h]=h(x) ∀x ⟹ h constant
├── ConstructiveGap.lean         # Proposition 1 (p:gap)
├── BridgeTheorem.lean           # Theorem 2 (t:bridge)
├── Necessity.lean               # Proposition 4 (p:necessity)
├── BridgeCorollary.lean         # Corollary 1 (c:bridge)
├── GeneralNonIdentification.lean  # Proposition 3 (p:general) [TODO]
├── Characterization.lean        # Theorem 1 (t:char) [TODO]
├── Rung3.lean                   # Prop 1§6 (p:rung3) [TODO]
├── VectorJacobian.lean          # Vector extension (p:jacobian) [TODO]
└── ElasticityGap.lean           # Corollary 2 (c:elas) [TODO]
```

### Dependency graph

```
ConstantOnSupport ──→ Characterization (t:char)
                  ──→ VectorJacobian (p:jacobian)
                  ──→ ElasticityGap (c:elas)

ConstructiveGap        (standalone)
GeneralNonIdentification (standalone, real analysis)

BridgeTheorem ──→ BridgeCorollary
Necessity     ──→ BridgeCorollary

Rung3 (standalone, definitional)
```

## Build

```bash
lake build
```

Requires Lean 4 v4.29.0 and Mathlib v4.29.0.

## Paper

[Albrecht and Traina (2026), "Abduction and the Demand Curve"](https://briancalbrecht.com/Albrecht-Traina-Demand-Curve.pdf)
