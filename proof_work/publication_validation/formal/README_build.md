# Direct Lean build in this container

`lake` package resolution is unreliable here, so the fixed Lean toolchain is
used directly. The pins are Lean `4.34.1` and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612` (see `lakefile.toml`,
`lean-toolchain`, and `lake-manifest.json`). Mathlib and the other pinned
packages are loaded through the `LEAN_PATH` assembled by `build_direct.sh`.

## What is formalized

The checked sources cover generic algebra and analysis used by the candidate:
interval endpoint operations, interval products and Bernstein enclosures,
quadratic-form/PSD interfaces, tree and domain semantics, candidate-family
energy identities, differentiation, stationary-point existence and uniqueness,
strict convexity, symmetry, and the final reduction statement. These are
reusable mathematical lemmas; they do not by themselves instantiate the
numerical global certificate.

The local arithmetic export supplies generated data for 12 complete local
classes (9 interior and 3 boundary), including 33 strictly positive LDL pivot
lower bounds and exact source-box/center containment facts. The exporter and
replay files are deliberately premise-oriented: actual real Hessian entries in
the stated intervals, the actual Hessian congruence binding, exact contact
and gradient identities, and boundary graph chain-rule/monotonicity bridges
remain outside this export. The replay has 147 operations (9*15 + 3*4).
Kernel verification of these new local modules is in progress and is awaiting
the parent verification run.

## Reproducibility commands

From the repository root:

```
python3 -u proof_work/publication_validation/export_local_lean.py --check
python3 -u proof_work/publication_validation/export_local_lean.py --self-test
python3 -u proof_work/publication_validation/export_local_ldl_replay.py --check
```

The direct compiler is sequential because Mathlib imports use substantial
memory:

```
cd proof_work/publication_validation/formal
./build_direct.sh Statement CoverageSoundness DomainCoverage Family CandidateMem \
  LocalCerts LocalLDLSemantics LocalLDLFactorization LocalLDLData LocalNonneg \
  IntervalLocalOps LocalLDLReplay GramBoundary LocalVerification
```

The project-root command below sets both PATH and LEAN_PATH and performs
compiler, root-module, axiom, and kernel checks sequentially:

```bash
python3 -B proof_work/publication_validation/verify_local_lean.py
```

For manual calls, export the PATH and full LEAN_PATH shown in `build_direct.sh`
in the calling shell; executing that script does not export its environment
back to the parent shell. The same toolchain can replay proof terms, one module
at a time:

```
leanchecker ThomsonNine.LocalCerts
leanchecker ThomsonNine.LocalLDLSemantics
leanchecker ThomsonNine.LocalLDLFactorization
leanchecker ThomsonNine.LocalLDLData
leanchecker ThomsonNine.LocalNonneg
leanchecker ThomsonNine.IntervalLocalOps
leanchecker ThomsonNine.LocalLDLReplay
leanchecker ThomsonNine.GramBoundary
leanchecker ThomsonNine.LocalVerification
```

For the already established generic and candidate-family sources, use the
module names recorded in `Axioms.lean` and run `leanchecker` serially. The
historical modules include `CoverageSoundness`, `DomainCoverage`, `Family`,
`CandidateMem`, `Derivative`, `Stationary`, `SecondDerivative`, `Minimum`,
`StrictConvex`, `EnergyContinuity`, `Applications`, `ContactInner`,
`EnergyBounds`, `DistanceValues`, `GramBound`, `DomainChamber`, `TreeSemantics`,
`PSDSemantics`, `Interval`, `IntervalTensor`, `IntervalMul`, `IntervalEval`,
`ThreePoint`, `ThreePointBound`, and `FinalAssembly`.

## Status and limits

The new local export and replay are awaiting kernel verification. This package
does not claim a checked numerical Hessian evaluation, the 45 exact contact
identities, boundary chain rules, or a closed final Thomson n=9 theorem. The
final theorem remains unproved: global tree coverage and certificate bindings,
exact contact/Hermite bridges, and the required residual nonnegativity
instantiation are still outside the formal sources. `#print axioms` on the
existing audit remains limited to Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`; this is not a claim that the new local
replay has already passed the kernel audit.
