# Lean project

One Lean 4 project, with Mathlib, for all the papers in this repository. Lean and Mathlib v4.36.0, pinned in
`lean-toolchain` and `lake-manifest.json`.

* `FreeDiagonal/Results.lean`: the statement of every formalized result, each proved by citing the
  library theorem that carries the work. Each paper's folder maps its statements to these names.
* `FreeDiagonal/Foundations/`, `Witness/`, `Graphs/`: minimum-rank completion (first paper).
* `FreeDiagonal/Closure/`, `Variety/`: closure rank and the factor-analysis varieties (second paper;
  it also uses `Foundations/` and `Witness/`).
* `FreeDiagonal/EvenComplementation/`: subgraph complementation at even k (third paper; it also uses
  `Foundations/`, `Witness/` and `Graphs/`). Its statements are in `EvenComplementation/Paper.lean`,
  named after the paper's numbering, not in `Results.lean`.

The only named hypothesis anywhere is `DSSExample18Q` (`FreeDiagonal/Variety/Example18.lean`), an
explicit argument of the two Theorem 6 statements of the factor-analysis paper.

## Build

Install Lean with [elan](https://github.com/leanprover/elan), then, in this folder:

    lake exe cache get      # download the compiled Mathlib
    lake build

## Axioms

    lake env lean PrintAxioms.lean

prints, for every theorem of `Results.lean` and every statement of `EvenComplementation/Paper.lean`, the axioms it uses; each should list only `propext`,
`Classical.choice` and `Quot.sound`. The repository's GitHub workflow runs the build and this check
on every push. The library contains no `sorry`, `axiom` declaration, `native_decide`, `unsafe`,
`implemented_by` or `opaque`.

`MD5SUMS.txt` lists the md5 of each file of this folder (`md5sum -c MD5SUMS.txt`).
