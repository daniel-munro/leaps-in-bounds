# Isosceles sets

## Where the records are

- `ionin-2009` settles n <= 8 and is the best summary of the history. Its Section 5 describes the largest sets for n <= 7, with coordinates for n = 6 and 7.
- Blokhuis' structure theorem (Theorem 2.15 of `ionin-2009`) reduces the problem to two-distance sets: an isosceles set with more than two distances splits into a two-distance set X and a set Y, in orthogonal affine subspaces, with every point of Y the center of a sphere containing X. Combined with the largest two-distance sets, this is how `ionin-2009` gets the exact values.

## Lower bounds for n >= 9

- The certificates for n = 9 to 12 are the midpoints of the edges of a regular n-simplex and its center, with C(n+1, 2) + 1 points. The midpoints are a two-distance set on a sphere about the center, so every triangle is isosceles. No source for these lower bounds has been found, so the site has them only as certificates.
- Other constructions tried on paper, all smaller for n = 9 to 12: a spherical isosceles set in R^(n-1), its center and the two points on the orthogonal axis at the sphere's radius (s + 3 points); and a spherical two-distance set X with a spherical isosceles set of the same radius around the same center in an orthogonal subspace, plus the center (for example 27 + 6 + 1 = 34 for n = 9). Lišonek's 45-point set in R^8 lies on two concentric spheres, not one, so it can't be extended by axis points.

## Upper bounds for n >= 9

- The site records only Blokhuis' bound C(n+2, 2).
- Bu, Gill and Yi (Zenodo, https://doi.org/10.5281/zenodo.23343351, September 2026, not peer reviewed) claim the largest two-distance sets in R^9 to R^12 have 45, 55, 66 and 78 points. Running the case analysis of Section 5 of `ionin-2009` with these values, and with the largest spherical two-distance sets, might settle n = 9 to 12, possibly at C(n+1, 2) + 1. A rough pass for n = 9 leaves 46 <= i(9) <= 48: the cases that don't close at once are X a two-distance set in R^8 with Y three points on an orthogonal line, and X two points with Y an isosceles set in R^8. Nothing here has been checked against a source.
