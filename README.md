# Research companion: formalizations and computations for papers

[![Lean build](https://github.com/StableAttractor/research-companion/actions/workflows/lean.yml/badge.svg)](https://github.com/StableAttractor/research-companion/actions/workflows/lean.yml)

Each paper has a folder of its own, which maps the paper's statements to Lean names and holds any
computation the paper reports. The Lean 4 / Mathlib formalization is a single project in
[`lean/`](lean/), built and checked by the GitHub workflow on every push; build instructions are in
its README.

| Paper | Folder |
|---|---|
| The Sharp 2k+2 Obstruction Bound for Minimum-Rank Completion with a Free Diagonal | [`minimum-rank-free-diagonal/`](minimum-rank-free-diagonal/) |
| The Sharp 2k+2 Threshold for Set-Theoretic Finiteness in Algebraic Factor Analysis | [`factor-analysis-threshold/`](factor-analysis-threshold/) |

Every result is proved from Lean's standard axioms only. Any hypothesis a paper's formalization
takes is stated in that paper's folder; at present there is one, used by Theorem 6 of the
factor-analysis paper.

As the papers' disclosure lines state, their arguments were produced by an AI system (Claude,
Anthropic) and have not yet been peer reviewed.
