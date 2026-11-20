# Fisher midpoint rigidity in exponential families

A local averaging identity determines a global probability law. In a regular minimal exponential family with flat Fisher metric, average two nearby models once in natural parameters and once in expectation parameters. If the Fisher midpoint of those averages agrees with the original Fisher midpoint on one open patch, a fixed invertible affine transformation of the sufficient statistic has independent Gaussian location and fixed-shape gamma coordinates at every natural tilt.

The same conclusion follows when the updated midpoint is merely equidistant from the endpoints, or when its displacement along each original Fisher chord is of order smaller than four. The converse holds for every pair in the maximal product family. The proof identifies the complete finiteness set, including divergence at each gamma boundary.

The [statement](Challenge.lean) gives the tests and the resulting equality of measures. The [proof guide](Proof.md) explains the normalization, the role of flatness and the relationship to earlier work. The [solution](Solution.lean) links the statements to the Lean proofs.

## Reproduce the checks

With the pinned Lean toolchain, run the following commands from the repository root.

```sh
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/check_contracts.py
lake comparator
```

The source check compares the independently elaborated statements and their referenced definitions using Lean's own Comparator algorithm. It also audits the permitted axioms. The independent symbolic examples use Python and SymPy 1.14.0.

```sh
python3 scripts/exact_replay.py
```

The Linux [verification workflow](.github/workflows/verify.yml) runs sandboxed Comparator and rechecks the exported proof with Lean, NanoDa and con-ron. The [metadata workflow](.github/workflows/metadata.yml) checks the upstream schema and the intake form's YAML parser. The proof uses the short-geodesic existence and remainder estimates from [EuclideanMidpointRigidity](https://github.com/JD-Jones-ASES/EuclideanMidpointRigidity/tree/4929a3c843e8b8c2905581575d9d5644694e0c79).
