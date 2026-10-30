# Certificates

A certificate claims a lower or upper bound on one constant and comes with evidence that a program can check, so the bound doesn't depend on trusting a paper or a secondary source. The site shows the strongest certificate on each side as the constant's **verified** bound, alongside the bounds from the literature.

Anyone, including an AI agent, can submit a certificate by opening a pull request that adds a file here. CI checks every certificate, and a new certificate must be strictly stronger than the existing ones for the same bound.

Only the families listed [below](#families) accept certificates so far.

## File format

One YAML file per certificate, in `certificates/<group>/`. The file name (without `.yml`) is the certificate ID and must be unique. By convention it's `<constant>-<lower|upper>-<value>.yml`.

```yaml
constant: ramsey-4-4      # constant ID, as on the site
bound: lower              # lower or upper
value: 18                 # the bound: R(4,4) >= 18 (an integer, or '\sqrt{m}' where the family allows it)
kind: witness             # witness or lean
witness:                  # for kind: witness (see the family's rules below)
  format: graph6
  data: 'PzlXWmJpZDeJEJbDgp\EJsWk'   # or `file: name.g6` for large witnesses
submitted_by: Your Name   # person or agent to credit
date: 2026-10-22          # submission date
source: greenwood-gleason-1955   # optional: key in source_data/sources.yml for where the construction comes from
notes: Paley graph of order 17.  # optional
```

For a Lean proof:

```yaml
kind: lean
lean:
  module: LeapsInBounds.Proofs.Ramsey33       # file in formal/, under LeapsInBounds/Proofs/
  theorem: LeapsInBounds.Proofs.Ramsey33.upper
```

## Kinds of evidence

### witness

An explicit construction, checked by a verifier for the constant's family in [`scripts/certificates.py`](../scripts/certificates.py). Witnesses suit bounds that come from a construction, which is how most new lower bounds on extremal quantities are found.

### lean

A theorem in the [`formal/`](../formal) Lean project whose type is exactly the family's formal statement of the bound, as defined in `formal/LeapsInBounds/Statements/`. The checker compiles the proof, then [`scripts/check_lean.lean`](../scripts/check_lean.lean) reads the compiled theorem and checks that:

- every declaration in the proof modules passes the Lean kernel, replayed on top of the trusted modules (so options like `debug.skipKernelTC` don't help);
- its type is the statement (syntactically, or else as checked by the kernel), built directly from the trusted statement's name and the certificate's numbers rather than parsed, so notation, macros or instances in the submission can't change what the statement means;
- the statement it refers to is the one in `formal/LeapsInBounds/Statements/` (a proof module that redeclares it fails to load);
- it depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. That rules out `sorry`, new axioms and `native_decide`.

Compiling a proof runs code from the submission, such as `#eval` or custom elaborators. CI compiles the proofs in a separate job with a read-only token, and the check job uses only the compiled proof modules, which it replays through the kernel rather than trusting. The check itself runs none of the submission's code.

The statement files are trusted: they define what every certificate means. Submissions should only add files under `formal/LeapsInBounds/Proofs/`. CI flags any pull request that changes the statements or the checking scripts.

## Graph witnesses

Families whose witnesses are graphs accept them in [graph6 or sparse6](https://users.cecs.anu.edu.au/~bdm/data/formats.txt) format (`format: graph6` or `format: sparse6`), with vertices numbered from 0. Use whichever is shorter: graph6 for dense graphs, sparse6 for sparse ones. By convention, witness files use the extensions `.g6` and `.s6`.

## Families

### Ramsey numbers: `ramsey-{r}-{s}`

Formal statements are in [`formal/LeapsInBounds/Statements/Ramsey.lean`](../formal/LeapsInBounds/Statements/Ramsey.lean):

- `LowerBound r s n` means `R(r,s) >= n`: some graph on `n - 1` vertices has no clique of size `r` and no independent set of size `s`.
- `UpperBound r s n` means `R(r,s) <= n`: every graph on `n` vertices has a clique of size `r` or an independent set of size `s`.

The same file proves that a lower bound never exceeds an upper bound, as a sanity check on the definitions.

Witnesses can certify lower bounds only. A witness for `R(r,s) >= n` is a graph on `n - 1` vertices with no `r`-clique and no independent set of size `s`.

### Van der Waerden numbers: `van-der-waerden-{r}-{k}`

Formal statements are in [`formal/LeapsInBounds/Statements/VanDerWaerden.lean`](../formal/LeapsInBounds/Statements/VanDerWaerden.lean):

- `LowerBound r k n` means `W(r,k) >= n`: some `r`-coloring of `n - 1` consecutive integers has no monochromatic arithmetic progression of length `k`.
- `UpperBound r k n` means `W(r,k) <= n`: every `r`-coloring of `n` consecutive integers has one.

Witnesses can certify lower bounds only. A witness for `W(r,k) >= n` uses `format: coloring`: a string of `n - 1` digits from `0` to `r - 1` (so `r <= 10`), the colors of consecutive integers, with no monochromatic arithmetic progression of length `k`. Whitespace is ignored.

### Cages: `cage-{k}-{g}`

Formal statements are in [`formal/LeapsInBounds/Statements/Cage.lean`](../formal/LeapsInBounds/Statements/Cage.lean):

- `LowerBound k g n` means `n(k,g) >= n`: no graph on fewer than `n` vertices is `k`-regular with girth `g`.
- `UpperBound k g n` means `n(k,g) <= n`: some graph on `n` vertices is `k`-regular with girth `g`.

Witnesses can certify upper bounds only. A witness for `n(k,g) <= n` is a `k`-regular graph of girth exactly `g` on `n` vertices.

### Degree-diameter problem: `degree-diameter-{d}-{k}`

Formal statements are in [`formal/LeapsInBounds/Statements/DegreeDiameter.lean`](../formal/LeapsInBounds/Statements/DegreeDiameter.lean):

- `LowerBound d k n` means `N(d,k) >= n`: some graph on `n` vertices has maximum degree at most `d` and diameter at most `k`.
- `UpperBound d k n` means `N(d,k) <= n`: every such graph has at most `n` vertices.

Witnesses can certify lower bounds only. A witness for `N(d,k) >= n` is a graph on `n` vertices with maximum degree at most `d` and diameter at most `k`.

### Minimal superpermutations: `minimal-superpermutation-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/Superpermutation.lean`](../formal/LeapsInBounds/Statements/Superpermutation.lean):

- `LowerBound n m` means `L(n) >= m`: every string containing all permutations of `n` symbols has length at least `m`.
- `UpperBound n m` means `L(n) <= m`: some such string has length at most `m`.

Witnesses can certify upper bounds only. A witness for `L(n) <= m` uses `format: string`: a string of at most `m` digits from `1` to `n` (so `n <= 9`) that contains every permutation of those digits as a contiguous substring. Whitespace is ignored.

### Kissing numbers: `kissing-number-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/KissingNumber.lean`](../formal/LeapsInBounds/Statements/KissingNumber.lean):

- `LowerBound n k` means `τ(n) >= k`: some `k` unit vectors in `ℝⁿ` are at distance at least 1 from each other (so unit spheres centered at twice these vectors touch the unit sphere at the origin without overlapping).
- `UpperBound n k` means `τ(n) <= k`: every such set of unit vectors has at most `k` vectors.

Witnesses can certify lower bounds only. A witness for `τ(n) >= k` uses `format: vectors`: `k` integer vectors, one per line with whitespace-separated entries, all with the same squared norm `N`, spanning a space of dimension at most `n` (they can have more than `n` coordinates), with every inner product between two of them at most `N / 2`. Normalized, these are unit vectors at angles of at least 60°, which is the same condition.

Large symmetric configurations can be given as a few seed vectors and a list of `symmetries`: signed permutations of the coordinates, each written as a list `s` of the numbers `±1` to `±m` in some order, mapping `x` to the vector whose `i`-th entry is `sign(s[i]) * x[|s[i]|]`. The configuration is then every image of the seeds under repeated symmetries, and must have exactly `k` vectors. The symmetries don't need to be symmetries of anything in particular: the checker only uses them to generate the vectors. For example, the 240 roots of `E_8` (scaled by 2):

```yaml
witness:
  format: vectors
  data: |
    2 2 0 0 0 0 0 0
    1 1 1 1 1 1 1 1
  symmetries:
  - [2, 1, 3, 4, 5, 6, 7, 8]     # swap the first two coordinates
  - [2, 3, 4, 5, 6, 7, 8, 1]     # cycle the coordinates
  - [-1, -2, 3, 4, 5, 6, 7, 8]   # negate the first two coordinates
```

### Packing unit squares in a square: `square-packing-in-square-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/SquarePacking.lean`](../formal/LeapsInBounds/Statements/SquarePacking.lean). A unit square is the image of `[0, 1]²` under an isometry of the plane, and a packing of `n` of them in `[0, s]²` has pairwise disjoint interiors.

- `SqrtLowerBound n m` means `s(n) >= √m`: no packing of `n` unit squares fits in a square of side less than `√m`.
- `SqrtUpperBound n m` means `s(n) <= √m`: `n` unit squares can be packed in a square of side `√m`.

Values can be integers `k` (proving the statement with `m = k²`) or square roots written `'\sqrt{m}'`, with `m` not a perfect square. Only Lean proofs are accepted so far.

## Checking locally

```bash
python scripts/check_certificates.py                # witnesses only
```

To also check Lean proofs, install [elan](https://github.com/leanprover/elan), then:

```bash
cd formal && lake exe cache get && lake build && cd ..
python scripts/check_certificates.py --lean
```

Add `--improves certificates/<group>/<file>.yml` to check that a new certificate beats the existing ones, as CI does.

## Known gaps

- Values are integers or square roots of integers for now. Other real values, such as most known square packings, will need exact or interval-arithmetic witnesses or more general statements.
- Kissing number witnesses must have integer coordinates (up to scaling). Some record configurations, such as those in dimensions 17 to 21, need irrational coordinates, so they can't be submitted yet.
