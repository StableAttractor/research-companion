# Research companion: formalizations and computations for papers

[![Lean build](https://github.com/StableAttractor/research-companion/actions/workflows/lean.yml/badge.svg)](https://github.com/StableAttractor/research-companion/actions/workflows/lean.yml)

Each paper has a folder of its own, which holds the paper, a table mapping its statements to Lean
names, and any computation the paper reports. The Lean 4 / Mathlib formalization is a single project in
[`lean/`](lean/), built and checked by the GitHub workflow on every push; build instructions are in
its README.

| Paper | Folder |
|---|---|
| The Sharp 2k+2 Obstruction Bound for Minimum-Rank Completion with a Free Diagonal ([PDF](minimum-rank-free-diagonal/paper/minimum-rank-free-diagonal.pdf)) | [`minimum-rank-free-diagonal/`](minimum-rank-free-diagonal/) |
| The Sharp 2k+2 Threshold for Set-Theoretic Finiteness in Algebraic Factor Analysis ([PDF](factor-analysis-threshold/paper/factor-analysis-threshold.pdf)) | [`factor-analysis-threshold/`](factor-analysis-threshold/) |

Every result is proved from Lean's standard axioms only. Any hypothesis a paper's formalization
takes is stated in that paper's folder; at present there is one, used by Theorem 6 of the
factor-analysis paper.

As the papers' disclosure lines state, their arguments were produced by an AI system (Claude,
Anthropic) and have not yet been peer reviewed.

## Licence and contact

The code in this repository (the Lean project and the scripts) is licensed under the Apache License,
Version 2.0; see [`LICENSE`](LICENSE). The papers in the `paper/` folders are not covered by that
licence; all rights in them are reserved. Contact: stableattractor@gmail.com.
