"""Graphs: witness formats, and the properties families check."""

from typing import Any, Iterator, Mapping

import numpy as np

from .errors import CertificateError
from .witness import read_witness_data


def decode_values(data: str, header: str) -> list[int]:
    """Convert graph6/sparse6 characters to 6-bit values, dropping the
    optional header."""
    data = data.strip()
    if data.startswith(header):
        data = data[len(header):]
    values = [ord(c) - 63 for c in data]
    if not values or any(v < 0 or v > 63 for v in values):
        raise CertificateError(f"Invalid {header.strip('<>')} data")
    return values


def decode_size(values: list[int]) -> tuple[int, list[int]]:
    """Read the number of vertices from the start of graph6/sparse6 values,
    returning it and the remaining values."""
    if values[0] < 63:
        return values[0], values[1:]
    if values[1] < 63:
        return (values[1] << 12) | (values[2] << 6) | values[3], values[4:]
    n = 0
    for v in values[2:8]:
        n = (n << 6) | v
    return n, values[8:]


def encode_size(n: int) -> list[int]:
    if n < 63:
        return [n]
    if n < 258048:
        return [63, (n >> 12) & 63, (n >> 6) & 63, n & 63]
    return [63, 63] + [(n >> (6 * k)) & 63 for k in range(5, -1, -1)]


def decode_graph6(data: str) -> list[int]:
    """Decode a graph6 string into a list of adjacency bitsets."""
    n, values = decode_size(decode_values(data, ">>graph6<<"))
    num_bits = n * (n - 1) // 2
    if len(values) != (num_bits + 5) // 6:
        raise CertificateError(f"graph6 data has wrong length for {n} vertices")
    bits = [(v >> (5 - k)) & 1 for v in values for k in range(6)]
    adj = [0] * n
    index = 0
    for j in range(1, n):
        for i in range(j):
            if bits[index]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            index += 1
    return adj


def encode_graph6(adj: list[int]) -> str:
    """Encode a list of adjacency bitsets as a graph6 string."""
    n = len(adj)
    values = encode_size(n)
    bits = [(adj[i] >> j) & 1 for j in range(1, n) for i in range(j)]
    bits += [0] * (-len(bits) % 6)
    for k in range(0, len(bits), 6):
        values.append(int("".join(map(str, bits[k:k + 6])), 2))
    return "".join(chr(v + 63) for v in values)


def decode_sparse6(data: str) -> list[int]:
    """Decode a sparse6 string into a list of adjacency bitsets.

    The data is a sequence of (b, x) pairs, with b one bit and x enough bits
    for n - 1. Keeping a current vertex v: b = 1 increments v, then x > v
    moves v to x, and otherwise gives the edge {x, v}. Padding is ignored.
    """
    data = data.strip()
    if data.startswith(">>sparse6<<"):
        data = data[len(">>sparse6<<"):]
    if not data.startswith(":"):
        raise CertificateError("sparse6 data must start with ':'")
    n, values = decode_size(decode_values(data[1:], ""))
    k = max(1, (n - 1).bit_length())
    bits = [(v >> (5 - i)) & 1 for v in values for i in range(6)]
    adj = [0] * n
    v = 0
    for index in range(0, len(bits) - k, k + 1):
        if bits[index]:
            v += 1
        x = int("".join(map(str, bits[index + 1:index + k + 1])), 2)
        if x >= n or v >= n:
            break
        if x > v:
            v = x
        elif x == v:
            raise CertificateError("sparse6 data contains a loop")
        else:
            adj[x] |= 1 << v
            adj[v] |= 1 << x
    return adj


def encode_sparse6(adj: list[int]) -> str:
    """Encode a list of adjacency bitsets as a sparse6 string."""
    n = len(adj)
    k = max(1, (n - 1).bit_length())
    edge_bits = []
    v = 0
    for high in range(n):
        for low in bits(adj[high] & ((1 << high) - 1)):
            if high == v:
                edge_bits.append([0, low])
            elif high == v + 1:
                edge_bits.append([1, low])
            else:
                edge_bits += [[1, high], [0, low]]
            v = high
    out = [b for flag, x in edge_bits for b in [flag] + [(x >> (k - 1 - i)) & 1 for i in range(k)]]
    padding = -len(out) % 6
    # Padding of 1s could otherwise decode as an extra edge {v + 1, n - 1}
    if k < 6 and n == 1 << k and padding >= k and v < n - 1:
        out.append(0)
    out += [1] * (-len(out) % 6)
    values = encode_size(n) + [int("".join(map(str, out[i:i + 6])), 2) for i in range(0, len(out), 6)]
    return ":" + "".join(chr(v + 63) for v in values)


def read_graph(cert: Mapping[str, Any]) -> list[int]:
    """Decode a graph witness in graph6 or sparse6 format."""
    decoders = {"graph6": decode_graph6, "sparse6": decode_sparse6}
    fmt = cert["witness"].get("format")
    if fmt not in decoders:
        raise CertificateError("Graph witnesses must use format: graph6 or sparse6")
    return decoders[fmt](read_witness_data(cert))


def complement(adj: list[int]) -> list[int]:
    n = len(adj)
    full = (1 << n) - 1
    return [full & ~adj[v] & ~(1 << v) for v in range(n)]


def has_clique(adj: list[int], k: int) -> bool:
    """Check whether a graph has a clique with k vertices."""
    return any(clique_search(adj, candidates, needed) for candidates, needed in clique_roots(adj, k))


def clique_roots(adj: list[int], k: int) -> list[tuple[int, int]]:
    """Searches, as (candidates, needed) pairs, that between them find a
    k-clique if the graph has one."""
    if k <= 0:
        return [(0, 0)]
    if is_circulant(adj):
        # Vertex-transitive, so any clique can be moved to contain vertex 0
        return [(adj[0], k - 1)] if adj else []
    return [((1 << len(adj)) - 1, k)]


def clique_search(adj: list[int], candidates: int, needed: int) -> bool:
    """Check whether some `needed` vertices among `candidates` form a clique."""
    if needed <= 1:
        return needed <= 0 or candidates != 0
    if candidates.bit_count() < needed:
        return False
    return any(clique_search(adj, sub, needed - 1) for sub in clique_branches(adj, candidates, needed))


def clique_branches(adj: list[int], candidates: int, needed: int) -> Iterator[int]:
    """Split the search for a clique of `needed` vertices (at least 2) among
    `candidates` into searches for `needed - 1` vertices among each yielded set.

    Branch and bound with a greedy colouring bound (Tomita and Seki's MCQ):
    the candidates are split into colour classes, sets of pairwise
    non-adjacent vertices, so a clique among them has at most one vertex per
    class. Vertices are tried in reverse colouring order, each with its
    neighbours among the candidates not yet tried, and once those (coloured
    before the current vertex, plus it) use fewer colours than the clique
    needs, no clique can be completed.
    """
    order = []
    colors = []
    uncolored = candidates
    color = 0
    while uncolored:
        color += 1
        available = uncolored
        while available:
            low = available & -available
            v = low.bit_length() - 1
            available &= ~adj[v] & ~low
            uncolored &= ~low
            order.append(v)
            colors.append(color)
    for i in range(len(order) - 1, -1, -1):
        if colors[i] < needed:
            return
        v = order[i]
        yield candidates & adj[v]
        candidates &= ~(1 << v)


def is_circulant(adj: list[int]) -> bool:
    """Check whether i -> i + 1 (mod n) is an automorphism of the graph."""
    n = len(adj)
    full = (1 << n) - 1
    return all(((adj[i] << 1) | (adj[i] >> (n - 1))) & full == adj[(i + 1) % n] for i in range(n))


def bits(mask: int) -> list[int]:
    """List the positions of the set bits in mask."""
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


def girth(adj: list[int]) -> float:
    """Length of the shortest cycle, or infinity if the graph is acyclic.

    BFS from each vertex: an edge within layer i closes a walk of length
    2i + 1, and a vertex in layer i + 1 with two neighbors in layer i closes
    one of length 2i + 2. Each such walk contains a cycle at most that long,
    and every shortest cycle is found this way from one of its vertices.
    """
    best = float("inf")
    for source in range(len(adj)):
        seen = layer = 1 << source
        depth = 0
        while layer and 2 * depth + 1 < best:
            if any(adj[v] & layer for v in bits(layer)):
                best = 2 * depth + 1
                break
            next_layer = 0
            for v in bits(layer):
                new = adj[v] & ~seen
                if new & next_layer:
                    best = min(best, 2 * depth + 2)
                next_layer |= new
            seen |= next_layer
            layer = next_layer
            depth += 1
    return best


def edge_arrays(adj: list[int]) -> tuple[np.ndarray, np.ndarray]:
    """The edges of a graph given by adjacency bitsets, as arrays of ends."""
    edges = [(u, v) for u in range(len(adj)) for v in bits(adj[u]) if u < v]
    ends = np.array(edges, dtype=np.int64).reshape(-1, 2)
    return ends[:, 0], ends[:, 1]


def check_simple(n: int, u: np.ndarray, v: np.ndarray) -> None:
    """Check that edges given by arrays of ends form a simple graph on n vertices."""
    if len(u) and (min(u.min(), v.min()) < 0 or max(u.max(), v.max()) >= n):
        raise CertificateError("Graph has an edge with an end that isn't a vertex")
    if np.any(u == v):
        raise CertificateError("Graph has a loop")
    keys = np.minimum(u, v) * n + np.maximum(u, v)
    if len(np.unique(keys)) != len(keys):
        raise CertificateError("Graph has a repeated edge")


def diameter_at_most(n: int, u: np.ndarray, v: np.ndarray, k: int) -> bool:
    """Check whether every two vertices of a graph, given by arrays of edge
    ends, are within distance k. Runs a breadth-first search from 512 vertices
    at a time, as bits of a word per vertex."""
    if n <= 1:
        return True
    ends = np.concatenate([u, v])
    degrees = np.bincount(ends, minlength=n)
    if not degrees.all():
        return False
    neighbors = np.concatenate([v, u])[np.argsort(ends, kind="stable")]
    starts = np.concatenate([[0], np.cumsum(degrees)[:-1]])
    words = 8
    batch = 64 * words
    for first in range(0, n, batch):
        roots = np.arange(first, min(first + batch, n))
        positions = roots - first
        reached = np.zeros((n, words), dtype=np.uint64)
        reached[roots, positions // 64] = np.left_shift(np.uint64(1), (positions % 64).astype(np.uint64))
        for _ in range(k):
            reached |= np.bitwise_or.reduceat(reached[neighbors], starts, axis=0)
        # Bits of the roots in this batch, which every vertex must have reached
        expected = np.zeros(batch, dtype=np.uint8)
        expected[:len(roots)] = 1
        expected = np.packbits(expected, bitorder="little").view(np.uint64)
        if np.any((reached & expected) != expected):
            return False
    return True


# Lines of the Hamming graph H(4,4), with vertices (x0, x1, x2, x3) numbered
# x0 + 4 x1 + 16 x2 + 64 x3: line 64 a + i varies coordinate a over 0 to 3,
# with the other coordinates, in increasing order, the base-4 digits of i.
HAMMING_LINES = np.array([
    [sum(((i >> 2 * j) & 3) << 2 * c for j, c in enumerate(c for c in range(4) if c != a)) + (t << 2 * a)
     for t in range(4)]
    for a in range(4) for i in range(64)
], dtype=np.int64)
HAMMING_LINES_MAGIC = b"H4LINE01"


def decode_hamming_lines(data: bytes) -> tuple[int, np.ndarray, np.ndarray]:
    """Decode a graph in hamming-lines format (see certificates/README.md),
    returning its number of vertices and arrays of edge ends."""
    if len(data) < 16 or data[:8] != HAMMING_LINES_MAGIC:
        raise CertificateError(f"hamming-lines witness must start with {HAMMING_LINES_MAGIC.decode()}")
    fibers = int.from_bytes(data[8:12], "little")
    clones = int.from_bytes(data[12:16], "little")
    lines = 256 * fibers
    if not 1 <= fibers <= 4096 or clones > lines:
        raise CertificateError(f"hamming-lines witness has {fibers} fibers and {clones} clones")
    width = (lines - 1).bit_length()
    count = lines + clones
    if len(data) != 16 + (count * width + 7) // 8:
        raise CertificateError(f"hamming-lines witness should have {16 + (count * width + 7) // 8} bytes, not {len(data)}")
    stream = np.unpackbits(np.frombuffer(data, dtype=np.uint8, offset=16), bitorder="little")
    if stream[count * width:].any():
        raise CertificateError("hamming-lines witness has padding bits that aren't 0")
    values = stream[:count * width].reshape(count, width).astype(np.int64) @ (np.int64(1) << np.arange(width))
    partners, sources = values[:lines], values[lines:]
    ids = np.arange(lines)
    if np.any(partners >= lines) or np.any(partners[np.minimum(partners, lines - 1)] != ids):
        raise CertificateError("hamming-lines partners must pair up the lines")
    if np.any(sources >= lines):
        raise CertificateError("hamming-lines clone source isn't a vertex of the base graph")
    vertices = 256 * (ids // 256)[:, None] + HAMMING_LINES[ids % 256]
    first = ids[ids < partners]
    u = np.repeat(vertices[first], 4, axis=1).ravel()
    v = np.tile(vertices[partners[first]], 4).ravel()
    # Each clone is joined to the neighbors of its source in the base graph
    base_degrees = np.bincount(np.concatenate([u, v]), minlength=lines)
    order = np.argsort(np.concatenate([u, v]), kind="stable")
    base_neighbors = np.concatenate([v, u])[order]
    base_starts = np.concatenate([[0], np.cumsum(base_degrees)])
    clone_u = np.repeat(lines + np.arange(clones), base_degrees[sources])
    clone_v = np.concatenate([base_neighbors[base_starts[s]:base_starts[s + 1]] for s in sources] or [np.zeros(0, np.int64)])
    return count, np.concatenate([u, clone_u]), np.concatenate([v, clone_v])
