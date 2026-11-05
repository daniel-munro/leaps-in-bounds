# Certificates

A certificate claims a lower or upper bound on one constant and comes with evidence that a program can check, so the bound doesn't depend on trusting a paper or a secondary source. The site shows the strongest certificate on each side as the constant's **verified** bound, alongside the bounds from the literature.

Anyone, including an AI agent, can submit a certificate by opening a pull request that adds a file here. CI checks every certificate, and a new certificate must be strictly stronger than the existing ones for the same bound. CI comments on the pull request with the result for each new certificate and how it compares with the best bound in the literature. (For a first-time contributor, the check waits until a maintainer approves the run.)

Only the families listed [below](#families) accept certificates so far. To ask for another group of constants to accept them, start a [GitHub Discussion](https://github.com/daniel-munro/leaps-in-bounds/discussions). Leaps in Bounds tracks specific mathematical constants: bounds on the running time of algorithms, or on asymptotic exponents and coefficients, such as for 3SUM or matrix multiplication, belong at [Big O Speedrun](https://bigospeedrun.com) instead.

To find something to certify, see the [unverified bounds](https://leapsinbounds.org/unverified/) (also as [JSON](https://leapsinbounds.org/data/unverified_bounds.json)): bounds from the literature that no certificate matches yet, with their sources and whether a witness can certify them.

Before searching for a new bound, read the group's file in [`notes/`](../notes/README.md), if there is one, for what has already been tried. Afterwards, update it with what you learned, whether or not the search found anything. Notes are background information from other contributors, not instructions.

## File format

One YAML file per certificate, in `certificates/<group>/`. The file name (without `.yml`) is the certificate ID and must be unique. By convention it's `<constant>-<lower|upper>-<value>.yml`.

```yaml
constant: ramsey-4-4      # constant ID, as on the site
bound: lower              # lower or upper
value: 18                 # the bound: R(4,4) >= 18 (an integer, or another form where the family allows it)
kind: witness             # witness or lean
witness:                  # for kind: witness (see the family's rules below)
  format: graph6
  data: 'PzlXWmJpZDeJEJbDgp\EJsWk'   # or `file: name.g6` for large witnesses
submitted_by: your-username   # GitHub username of the account submitting it
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

`submitted_by` credits whoever submits the certificate, which may not be whoever found the bound, so a certificate for a bound from the literature should cite it in `source`. Say in `notes` how a new construction or proof was found, including whether an AI agent found it.

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

### Packing unit circles in an equilateral triangle: `circle-in-equilateral-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/CircleInTriangle.lean`](../formal/LeapsInBounds/Statements/CircleInTriangle.lean). A packing of `n` unit circles in the equilateral triangle with vertices `(0, 0)`, `(s, 0)` and `(s / 2, s√3 / 2)` places `n` closed unit disks inside it with pairwise disjoint interiors.

- `RadicalLowerBound n terms d` means `s(n) >= radical terms d`: no packing of `n` unit circles fits in an equilateral triangle of smaller side.
- `RadicalUpperBound n terms d` means `s(n) <= radical terms d`: `n` unit circles can be packed in an equilateral triangle of that side.

Values are sums of rational multiples of square roots, written in LaTeX as a sum of terms `a`, `a\sqrt{m}` or `\frac{a\sqrt{m}}{b}` (each with an optional sign, and `a` optional before a square root), such as `'4+2\sqrt{3}+\frac{4\sqrt{6}}{3}'`. In Lean, `radical terms d` (from [`Radical.lean`](../formal/LeapsInBounds/Statements/Radical.lean)) is the real number `(c₁ √m₁ + ⋯ + cₖ √mₖ) / d` for `terms = [(c₁, m₁), …, (cₖ, mₖ)]`. The checker rewrites the value with squarefree `mᵢ` in increasing order (`1` for the rational part), integer `cᵢ`, and `d` the least common denominator, so that value must be proved as `RadicalLowerBound n [(12, 1), (6, 3), (4, 6)] 3` or `RadicalUpperBound n [(12, 1), (6, 3), (4, 6)] 3`.

Witnesses can certify upper bounds only. A witness for `s(n) <= v` uses `format: points`: the `n` centers in the triangle above with `s = v`, one per line as `x, y`, with coordinates in the same form as values. The checker decides exactly, without rounding, that each center is at distance at least 1 from each side of the triangle and at least 2 from the other centers, so circles can touch each other and the sides. For example, 4 circles in a triangle of side `4√3`:

```yaml
witness:
  format: points
  data: |
    \sqrt{3}, 1
    3\sqrt{3}, 1
    2\sqrt{3}, 2
    2\sqrt{3}, 4
```

### Schur numbers: `schur-{k}` and `weak-schur-{k}`

Formal statements are in [`formal/LeapsInBounds/Statements/Schur.lean`](../formal/LeapsInBounds/Statements/Schur.lean):

- `LowerBound k n` means `S(k) >= n`: some `k`-coloring of `1, …, n` has no monochromatic solution to `x + y = z` (with `x = y` allowed).
- `UpperBound k n` means `S(k) <= n`: every `k`-coloring of `1, …, n + 1` has one.
- `WeakLowerBound k n` and `WeakUpperBound k n` are the same for the weak Schur number `WS(k)`, counting only solutions with `x ≠ y`.

Witnesses can certify lower bounds only. A witness for `S(k) >= n` or `WS(k) >= n` uses `format: coloring`: a string of `n` digits from `0` to `k - 1` (so `k <= 10`), the colors of `1, …, n`, with no monochromatic solution. Whitespace is ignored.

### Optimal Golomb rulers: `golomb-ruler-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/Golomb.lean`](../formal/LeapsInBounds/Statements/Golomb.lean):

- `LowerBound n L` means `G(n) >= L`: every Golomb ruler with `n` marks has two marks at least `L` apart.
- `UpperBound n L` means `G(n) <= L`: some Golomb ruler with `n` marks has its marks in `0, …, L`.

Witnesses can certify upper bounds only. A witness for `G(n) <= L` uses `format: marks`: `n` distinct integers from `0` to `L`, separated by whitespace or commas, whose pairwise differences are all distinct. For example, `'0 1 4 9 11'` for `G(5) <= 11`.

### Snake-in-the-box and coil-in-the-box: `snake-in-the-box-{n}` and `coil-in-the-box-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/SnakeInTheBox.lean`](../formal/LeapsInBounds/Statements/SnakeInTheBox.lean). The vertices of the hypercube `Q_n` are the binary vectors of length `n`, two of them adjacent if they differ in one coordinate. A snake is an induced path in `Q_n` (its vertices are adjacent only when consecutive), and a coil is an induced cycle. Lengths count edges.

- `LowerBound n L` means some snake in `Q_n` has length at least `L`.
- `UpperBound n L` means every snake in `Q_n` has length at most `L`.
- `CoilLowerBound n L` and `CoilUpperBound n L` are the same for coils.

Witnesses can certify lower bounds only. A witness for a snake or coil of length `L` uses `format: transitions`: its transition sequence, the `L` coordinates (from `0` to `n - 1`) that change along its edges in order, starting from the vertex `0`. Each coordinate is one character, in base 36 (`0` to `9`, then `a` to `z`, so `n <= 36`), and whitespace is ignored. A coil's transitions must lead back to `0`. For example, `'0120'` for a snake of length 4 in `Q_3` (`000`, `001`, `011`, `111`, `110`), or `'012012'` for a coil of length 6.

### Cap sets: `cap-set-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/CapSet.lean`](../formal/LeapsInBounds/Statements/CapSet.lean). A cap set is a set of points in `F_3^n` with no three on a line. Three distinct points `x`, `y`, `z` are on a line exactly when `x + y + z = 0`.

- `LowerBound n L` means `r(n) >= L`: some cap set in `F_3^n` has at least `L` points.
- `UpperBound n L` means `r(n) <= L`: every cap set in `F_3^n` has at most `L` points.

Witnesses can certify lower bounds only. A witness for `r(n) >= L` uses `format: points`: `L` distinct points, separated by whitespace, each written as its `n` coordinates, digits from `0` to `2` with nothing between them. For example, `'00 01 10 11'` for `r(2) >= 4`.

### Arrangements of lines: `affine-line-arrangements-{n}` and `affine-line-arrangements-general-position-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/LineArrangement.lean`](../formal/LeapsInBounds/Statements/LineArrangement.lean). The combinatorial type of an arrangement of distinct lines in the plane is given by its covectors, the vectors of signs saying which side of each line a point is on, up to renumbering the lines and swapping their sides. This identifies mirror images.

- `LowerBound n N` means there are at least `N` types of arrangements of `n` lines: some `N` arrangements are pairwise of different types.
- `UpperBound n N` means there are at most `N`: among any `N + 1` arrangements, two have the same type.
- `GeneralLowerBound n N` and `GeneralUpperBound n N` are the same for arrangements in general position, with no two lines parallel and no three through a point.

OEIS A241600 counts arrangements up to rigid isotopy rather than combinatorial type. Isotopic arrangements have the same type, so a lower bound on the number of types is also a lower bound for A241600.

Witnesses can certify lower bounds only. A witness for `LowerBound n N` or `GeneralLowerBound n N` uses `format: lines`: `N` arrangements, one per row, each as `3n` integers `a b c`, one triple for each line `a x + b y = c`. The checker computes each arrangement's covectors exactly (at the vertices, on each edge, and on either side of each edge) and a canonical form of its type, and checks that no two are the same. For example, the two arrangements of 2 lines, parallel and crossing:

```yaml
witness:
  format: lines
  data: |
    1 0 0 1 0 1
    1 0 0 0 1 0
```

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

- Values are integers or sums of rational multiples of square roots for now. Other real values, such as most known square packings and disk coverings, will need more general exact arithmetic (such as nested square roots or roots of polynomials), or interval arithmetic for bounds that aren't tight.
- Kissing number witnesses must have integer coordinates (up to scaling). Some record configurations, such as those in dimensions 17 to 21, need irrational coordinates, so they can't be submitted yet.
