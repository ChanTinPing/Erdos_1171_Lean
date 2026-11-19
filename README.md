# Erdős Problem #1171 in Lean 4

This repository proves the finite-color ordinal partition relation in Erdős Problem #1171, also listed as **JSP-000976** in the Justin Sun Prize catalog. The formal proof uses a direct combinatorial argument. [Original problem](https://www.erdosproblems.com/1171) · [Prize catalog](https://github.com/TheJustinSunPrize/awards/blob/10e0ab6e7503b6db769029d7d68cc4ca42c011d7/problems/catalog-0901-1000.md#JSP-000976)

## Statement

Write $\omega_1$ for the first uncountable ordinal and $\omega$ for the order type of the natural numbers. For every natural number $k$, every coloring of the unordered pairs of $\omega_1^2$ by $0,1,\ldots,k$ has either a color-zero homogeneous set of inherited order type $\omega_1\cdot\omega$ or a monochromatic triangle of a nonzero color. All arithmetic on ordinals in this statement is ordinal arithmetic.

```lean
theorem erdos_1171 : Jsp000976.Statement
```

The [submission theorem](formalization/jsp-000976/Jsp000976/Theorem.lean) is `Jsp000976.erdos_1171`. The [statement audit](formalization/jsp-000976/Audit.lean) applies it to the fully expanded unordered-pair formulation and the equivalent symmetric-function formulation. [Lean statement](formalization/jsp-000976/Jsp000976/Statement.lean) · [Formal Conjectures reference](https://github.com/google-deepmind/formal-conjectures/blob/b576d527b271b936f9e61c0e367c302d7386bc80/FormalConjectures/ErdosProblems/1171.lean)

## Proof outline and attribution

Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer proved the result in Theorem 1.1 of *A finite-color partition relation for ω₁²*. This project follows their nested-coloring and backward-incidence reductions and retains the idea of increasing the set of marked colors. [Preprint, Hexagon 2611.00584v1](https://hexagonmath.org/2611.00584v1)

**Where this proof differs.** The preprint uses a category principle in §4 to find a single branch meeting all finite requirements. In §5 it obtains that principle by Cohen forcing and reflects the homogeneous set to the ground model. The Lean proof counts marked colors in a family of slices indexed by paths in the reservoir tree. Each finite collection of requirements has its own infinite chain. Sets of labels containing no infinite chain, together with the old marks, generate a proper ideal. Minimizing the colors on edges between comparable labels then marks a new color. This gives the induction directly, with no category hypothesis, forcing, or reflection. [Detailed comparison and mathematical proof](formalization/jsp-000976/ground-proof.md)

1. Reduce to a nested coloring and derive backward incidence in a full region. [Nested reduction](formalization/jsp-000976/Jsp000976/Nested.lean) · [Incidence](formalization/jsp-000976/Jsp000976/Incidence.lean)
2. Keep full child reservoirs that meet finite tests. Index slices in a subtree of one dense marked-color type and generate the proper ideal. [Reservoir tree](formalization/jsp-000976/Jsp000976/PrunedFamilies.lean) · [Chain ideal](formalization/jsp-000976/Jsp000976/ChainIdeal.lean)
3. Thin compatible slices, minimize their positive palette, and extend the marks. The induction leads to the contradiction that all positive colors are marked. The ordinal grid isomorphism transports the resulting zero stock to the required order type. [Marking step](formalization/jsp-000976/Jsp000976/GroundStep.lean) · [Ordinal correspondence](formalization/jsp-000976/Jsp000976/Geometry.lean)

The Lean project is maintained by [@ChanTinPing](https://github.com/ChanTinPing). It uses Lean 4.34.1 and a pinned revision of [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612).

## Verify the proof

With Git, Elan, and PowerShell 7 installed, run this from the repository root.

```powershell
pwsh -NoProfile -File ./Verify.ps1
```

The verifier installs the pinned toolchain if needed and obtains the Mathlib cache for the imported modules. It rebuilds the 18 proof modules serially in a fresh output directory, replays them with `leanchecker`, and checks the statement and transitive axioms. It accepts only `propext`, `Classical.choice`, and `Quot.sound`. Build and audit output is saved in `.lake/verify/proof-build.log`. [Verification script](Verify.ps1)
