"""Helpers for checkers that read a witness as a stream of rows, check them in
batches in parallel, and count the distinct objects among them by hash. A
checker built this way can read a generator's output of any size, limited only
by the time it takes."""

import collections
import itertools
import os
from concurrent.futures import Future, ProcessPoolExecutor
from typing import Any, Callable, Iterator

import numpy as np


def batches(rows: Iterator[str], size: int) -> Iterator[tuple[int, list[str]]]:
    """The non-blank rows, in batches, with the number of the first in each."""
    batch: list[str] = []
    first = 1
    for row in rows:
        if row.strip():
            batch.append(row)
            if len(batch) == size:
                yield first, batch
                first += size
                batch = []
    if batch:
        yield first, batch


def map_batches(func: Callable[..., bytes], rows: Iterator[str], size: int, *args: Any) -> Iterator[bytes]:
    """func(batch, *args, first) for each batch of rows, in order, run in
    parallel if there's more than one batch. Only a few batches per process are
    read ahead, so the rows are never all in memory."""
    chunks = batches(rows, size)
    first_batch = next(chunks, None)
    second_batch = next(chunks, None)
    if first_batch is None:
        return
    if second_batch is None:
        yield func(first_batch[1], *args, first_batch[0])
        return
    workers = os.cpu_count() or 1
    with ProcessPoolExecutor(max_workers=workers) as pool:
        pending: collections.deque[Future[bytes]] = collections.deque()
        for first, batch in itertools.chain([first_batch, second_batch], chunks):
            if len(pending) >= 2 * workers:
                yield pending.popleft().result()
            pending.append(pool.submit(func, batch, *args, first))
        while pending:
            yield pending.popleft().result()


def count_distinct(digests: Iterator[bytes]) -> tuple[int, int]:
    """The number of 8-byte digests, and the number of distinct ones. They're
    kept sorted and without repeats, merging new ones in now and then: 8 bytes
    of memory per distinct digest."""
    distinct = np.zeros(0, dtype=np.uint64)
    new: list[np.ndarray] = []
    total = waiting = 0
    for chunk in digests:
        new.append(np.frombuffer(chunk, dtype=np.uint64))
        total += len(new[-1])
        waiting += len(new[-1])
        if waiting >= 1 << 24:
            distinct = np.unique(np.concatenate([distinct, *new]))
            new, waiting = [], 0
    distinct = np.unique(np.concatenate([distinct, *new]))
    return total, len(distinct)
