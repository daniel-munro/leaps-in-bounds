# Rectilinear crossing number

## Where the records are

- Oswin Aichholzer's Rectilinear Crossing Number project page at TU Graz (`aichholzer-crossing-page`) has the lower bounds and best known point sets (`best028.asc` and so on) for n <= 100. Its table was last modified 2015-05-26. The page refused connections on 2026-11-12; the bounds here were read from a Wayback Machine capture of 2022-02-14. The point set files themselves haven't been fetched, so they aren't certificates yet.
- `abrego-et-al-2011`, Section 6, lists lower bounds for 28 <= n <= 99 (on the pseudolinear crossing number, which is at most the rectilinear one). They match the page's lower bounds.
- `fabila-monroy-lopez-2014`, Table 1, improved the best point sets for many n from 46 to 99 by local search, and lists the previous best for each. The paper prints its 75-point set with 450492 crossings (the certificate for n = 75); its other sets are said to be on its arXiv page.

## Searches

All in C with 64-bit integer coordinates (128-bit orientation tests in the symmetric search), recounting only the 4-point subsets that contain a moved point.

- Simulated annealing that moves one point at a time to a random nearby integer point, with move sizes spread over six orders of magnitude, starting from points in three clusters at the corners of a triangle, with restarts from the best set every 200000 moves.
  - Reached the known value within seconds for n <= 23 and for n = 25, from each of three seeds.
  - Fell short within 5 to 15 minutes per run (best of 3 to 6 seeds): n = 24 by 1, n = 26 by 1 (5251), n = 27 by 4 until a longer run reached 6180, n = 28 by 3 against the best known 7234 (7237), and n = 30 by 8. It reached 8423 for n = 29, matching the best known.
  - Occasionally jumping a point next to another random point didn't help for n = 24.
- The same annealing restricted to point sets with 3-fold rotational symmetry (n = 3k, k orbits, rotated points rounded to integers at scale 10^9) reached the optimum for n = 24, 27 and 30 in 15 minutes for one or more of three seeds.
- Warm starts didn't help: starting from the n = 23 set plus a point for n = 24, or from the n = 27 and 29 sets minus a point for n = 26 and 28 (5263 and 7250 before annealing), ended no better than fresh runs.
- For n <= 12, the same annealing on a 61 x 61 grid reaches the optimum within seconds. The certificates for n <= 12 are the optimal sets, among 200 seeds, whose vertices and crossings are farthest apart, then hill-climbed to spread them further, so that they draw clearly.
- Not yet tried: the 3-fold symmetric search with a fixed point or orbit structure for n = 26 and 28 (n not divisible by 3), longer runs, or starting from the page's point sets.

## Verified lower bounds from the Harary–Hill formalization

No `rectilinear-crossing-*` constant has a verified lower bound yet. OpenAI formalized in Lean that the crossing number of `K_n` (drawings with curved edges) is Hill's `Z(n) = floor(n/2) floor((n-1)/2) floor((n-2)/2) floor((n-3)/2) / 4` ([openai/math](https://github.com/openai/math) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, challenge statement `lean/ComparatorChallenges/CompleteCrossing.lean`, proof `OAI.Paper170.complete_graph_lower_bound` in `lean/OAI/Combinatorics/CompleteCrossing/Main.lean`; Prove2Me has a port). Every straight-line drawing is such a drawing, so `cr̄(K_n) >= Z(n)`. Assessed 2026-11-12; nothing has been submitted.

What it would give: `Z(n)` = 1, 3, 9, 18, 36 for n = 5 to 9, which is exact for n = 5, 6, 7 and 9 (cr̄(K_8) = 19). For n >= 10 it is below the known values (60 against 62 for n = 10, 9555 against 9726 for n = 30), but it would be the first verified lower bound for every n.

### The bridge

OpenAI's `AdmissibleDrawing` counts crossing *points* and requires edges to cross properly (a local chart taking the two edges to the axes) and no three edge interiors to share a point (`no_triples`). Ours counts crossing *pairs* of straight edges with the vertices in general position, where three or more diagonals can be concurrent. So a lemma is needed: if every admissible drawing of `K_n` has at least `c` crossings, then `LowerBound n c`. Plan:

1. **Perturb** the points so that no three edges are concurrent, keeping general position and creating no new crossing pairs. Move the vertices one at a time, in order. When moving vertex `v`, stay within a radius `δ` small enough that each pair of disjoint closed segments with an end at `v` stays disjoint (they are compact, and the segment moves by at most the distance `v` moves), and avoid finitely many lines: the line through each two other vertices (keeps general position and distinctness), and, for each pair of crossing edges not at `v` meeting at `X` and each other vertex `w`, the line `wX` (so edge `vw` doesn't pass through `X`). Lines have Haar measure zero (`MeasureTheory.Measure.addHaar_affineSubspace`), so they can't cover a ball. A concurrent triple of edges has six distinct ends; once the last of them has moved, the triple is no longer concurrent, and later moves don't touch it.
2. **Admissible drawing** from the perturbed points `q`: edges `Path.segment`, whose interior is `openSegment`. Injectivity of edges and vertex avoidance follow from general position, finiteness from two non-collinear segments meeting at most once, and proper crossings from the affine chart in OpenAI's `Zarankiewicz.properCrossing_openSegments` (`lean/OAI/Combinatorics/Crossing/ProperSegmentCrossing.lean`), which can be adapted to `Paper170.ProperCrossing`.
3. **Counting**: each crossing point lies on two distinct edges, which then share no vertex and so form a crossing pair; so `crossingCount ≤ crossings q ≤ crossings p`.

A skeleton with these statements (the `Paper170` definitions copied verbatim, five lemmas left as `sorry`, the final step proved) type-checks against the `formal/` toolchain (Lean v4.35.0). Estimated size of the full bridge: 600 to 1200 lines of plane geometry, all standard; step 1 is the bulk of it. It doesn't depend on OpenAI's proof, only on the challenge statement's definitions, so it can be written and checked on its own.

### Getting OpenAI's proof here

The lower bound needs 300 of OpenAI's modules (`OAI/Combinatorics/CompleteCrossing` and `OAI/Combinatorics/Crossing`): 33,400 lines, 1.46 MB, importing only Mathlib and Lean core, with no `sorry`, axioms or `native_decide` (by grep). It is Apache-2.0, which allows copying it here (MIT) with its license and a note of changes. OpenAI's project uses Lean v4.34.1 and a Mathlib from before v4.35.0.

All 300 modules compile unchanged against `formal/`'s Lean v4.35.0 and Mathlib (tried 2026-11-12, out of tree, using `lake env lean` with `formal/`'s `LEAN_PATH`). That took 36 minutes of wall time with 6 parallel jobs on an 8-core laptop, about 54 CPU-minutes. `#print axioms OAI.Paper170.complete_graph_lower_bound` gives only `propext`, `Classical.choice` and `Quot.sound`. Its type is `∀ n, 3 ≤ n → ∀ D : AdmissibleDrawing (completeGraph n), hill n ≤ crossingCount D`, where `AdmissibleDrawing` and `crossingCount` are the development's own definitions. They should match the challenge file's, which OpenAI's comparator checks, but the bridge would be stated against the development's definitions directly. So the toolchain is not the obstacle. Size and trust are.

Routes, from most to least verified:

- **Copy it under `formal/LeapsInBounds/Proofs/`** (for example `Proofs/HararyHill/...`), so `check_lean.lean` replays every declaration through the kernel. Its 1.46 MB is about three times the 500 kB evidence limit, so this needs a maintainer decision: an exemption for a shared library, or counting it once rather than per certificate (`evidence_files` follows every imported `LeapsInBounds.Proofs` module, so each of the five certificates would include all of it in its hash). Every later toolchain bump would have to keep it compiling.
- **Copy it outside `Proofs/`** (or require a pinned fork as a Lake dependency): not counted, but `check_lean.lean` treats every non-`Proofs` module as trusted and doesn't replay it, which weakens what "verified" means unless the checker is changed to replay it too.
- **Attestation**: someone builds the bridge on top of OpenAI's repository at a pinned commit, with a verbatim copy of our statement. The bound would show as attested, not verified. The certificate format doesn't accept this yet: `kind: lean` needs a module in `formal/`, and attestations are written for witnesses, so it needs a format change too, and a maintainer has to compare the copied statement with ours by hand.

Whichever route is taken, the bridge is the new work, and it is needed by all three. A cheaper partial alternative that needs none of OpenAI's code: Klein's theorem (any 5 points in general position include 4 in convex position) gives `cr̄(K_5) >= 1`, and averaging over subsets gives `cr̄(K_{n+1}) >= ceil((n+1) cr̄(K_n) / (n-3))`, which reaches 3 for n = 6 but only 7 for n = 7.
