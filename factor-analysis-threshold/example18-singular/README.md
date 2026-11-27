# Reproduction of [DSS07, Example 18] in Singular

Theorem 6 of the paper takes as its one hypothesis the outcome of the computation in Example 18 of
Drton, Sturmfels and Sullivant, *Algebraic factor analysis: tetrads, pentads and beyond*
(arXiv:math/0509390). This folder repeats that computation over ℚ.

**Step 1, `ex18_p8_elim.sing`** (about 1 minute). The ring and commands printed in Example 18:
the 4 × 4 minors of the generic symmetric 8 × 8 matrix `Psi` (diagonal entries included as
variables), elimination of the diagonal variables, and a minimal generating set (`mstd`).
It writes the generators to `ex18_I83min.txt`.

**Step 2, `ex18_p8_J_Q.sing`** (about 30 minutes on one core). It reads `ex18_I83min.txt`, forms
J_{8,3} from the 35 off-diagonal 4 × 4 minors and the septads (`septads.lib`, from the definition of
the linear eliminants in [DSS07, Corollary 10] with R ∪ C = R̄ ∪ C̄), computes a Gröbner basis of
J_{8,3} truncated at degree 16, and tests each generator and the square of each generator for
membership. The squares have degree at most 16, so the truncated basis decides membership exactly.

Run both from this folder (Singular 4.3 or later; standard input must be redirected, or Singular
waits for input):

    Singular -q ex18_p8_elim.sing < /dev/null
    Singular -q ex18_p8_J_Q.sing  < /dev/null

Expected output (`logs/`, from Singular 4.3.2; the "redefining" and "no standard basis" warnings
are removed from the logs):

* step 1: 442 minimal generators, 14 of degree 4, 260 of degree 7 and 168 of degree 8, as printed in
  [DSS07]; codimension 7, degree 1368. `ex18_I83min.txt` has md5 `73bd5939bae0769604a53129c43223d8`;
* step 2: 134 generators lie in J_{8,3} (14 of degree 4, 120 of degree 7); the squares of the other
  308 all lie in J_{8,3}: `squares in J: deg7 140 deg8 168 not in J: 0`.

In Lean, `paper_v4_example18_of_generators` turns exactly these two facts (a generating set of the
elimination ideal, each member in J_{8,3} or with its square there) into the hypothesis
`DSSExample18Q`. That the Singular commands compute what they are documented to compute is not
formalized; that is what the hypothesis stands for.
