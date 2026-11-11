# Degree-diameter notes

## Initial lower bounds for d up to 20 and k up to 10 (2026-11)

Every constant from d = 4 to 20 and k = 3 to 10 without a verified lower bound got one from a random Cayley graph of a metacyclic group: Z_m ⋊ Z_s with product (a, b)(c, e) = (a + r^b c, b + e), where r^s ≡ 1 (mod m), and a random inverse-closed connection set of size at most d. The search was a small C program. Cayley graphs are vertex-transitive, so it needs only one BFS from the identity per candidate. For each order N it picks random (m, s, r) and random connection sets. Each certificate's notes give the group and connection set, so the graph can be rebuilt.

**Cap of 4000 vertices.** The checker in `scripts/certificates.py` runs a bitset BFS from every vertex on Python big integers, which costs roughly n³/64 word operations. On a lightly loaded machine, n = 3000 takes about 8 s of CPU time and n = 4000 about 20 s. Bigger graphs fit easily within the 500 kB limit (sparse6 for n = 4000 and d = 20 is about 90 kB), so time is what limits them. With 112 certificates, 4000 vertices was the cap, so most of these constants have a bound of exactly 4000. That cap is far below the records (up to about 10¹¹). At n = 4000, a few thousand random tries usually found a graph at once. That worked for 97 of the 112, and for (6,6) and (13,4) with more tries.

**Constants below the cap**, from searching downward in N from min(4000, record) with a few thousand tries per order, plus a sparser second pass:

| (d,k) | found | record |
|---|---|---|
| (4,8) | 2943 | 3243 |
| (4,9), (5,7) | 3996 | 7884, 6000 |
| (5,6) | 1554 | 2836 |
| (7,5) | 2394 | 2810 |
| (8,5) | 3955 | 5334 |
| (10,4) | 2041 | 2556 |
| (11,4) | 2500 | 3645 |
| (12,4) | 3976 | 6156 |
| (17,3) | 1140 | 2210 |
| (18,3) | 1421 | 2210 |
| (19,3) | 1500 | 2783 |
| (20,3) | 1771 | 2796 |

At order exactly 4000, 10⁶ tries failed for (4,9), (5,7), (8,5) and (12,4), so those stayed just below the cap. For (5,6), 60000 tries at each order from 1600 to 2400 in steps of 16 found nothing. Metacyclic groups seem weak for degree 5 and diameter 6, or the search needs a better strategy than uniformly random generators. Diameter 3 with degree 17 to 20 is also well short of the records.

## Ideas

- A faster checker, such as numpy, or BFS from one vertex for a Cayley graph given by its group and generators, would lift the cap. Most of these constants would then go up to whatever the checker can handle.
- The small-k constants (k = 3 and 4 with d ≥ 10) and (5,6), (7,5) are the ones where better constructions matter, because the records are within reach of the cap. Options: other group families (semidirect products with non-cyclic kernels, as in Loz's and the Exoo tables), hill-climbing on the connection set instead of independent random tries, and known algebraic constructions for diameter 3, such as voltage graphs over Brown polarity graphs.
- Cartesian products of existing witnesses (degrees add and diameters add) and undirected Kautz graphs were much worse than random Cayley graphs here, so they weren't used.
