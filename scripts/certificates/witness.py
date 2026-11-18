"""Read witnesses: inline data or files here, possibly compressed."""

import lzma
import pathlib
import zlib
from typing import Any, Mapping

from .errors import CertificateError


# Witness files can be compressed with gzip or xz, by their extension, up to
# this many bytes uncompressed
COMPRESSED_SUFFIXES = [".gz", ".xz"]
MAX_UNCOMPRESSED_BYTES = 200_000_000

# Symbols for colorings and strings with more than 10 colors or symbols
BASE36 = "0123456789abcdefghijklmnopqrstuvwxyz"


def read_witness_file(cert: Mapping[str, Any]) -> bytes:
    """The bytes of a witness file here, decompressed if it ends in .gz or .xz,
    or the output of a generator witness that has been run (see generator.py)."""
    witness = cert["witness"]
    if "generated" in witness:
        return witness["generated"]
    if witness.get("format") == "generator":
        raise CertificateError(f"{cert['id']}: the witness is a generator, which has to be run to read it")
    if "file" in witness:
        path = pathlib.Path(cert["path"]).parent / witness["file"]
        data = path.read_bytes()
        if path.suffix in COMPRESSED_SUFFIXES:
            data = decompress(data, path.suffix, f"{cert['id']}: {path}")
        return data
    if "url" in witness:
        raise CertificateError(f"{cert['id']}: the witness is only linked, at {witness['url']}, so it can't be checked here")
    raise CertificateError(f"{cert['id']}: witness needs 'file' or 'url'")


def read_witness_data(cert: Mapping[str, Any]) -> str:
    """The witness as text: inline data, a file here, decompressed if it ends
    in .gz or .xz, or the output of a generator."""
    if "data" in cert["witness"]:
        return cert["witness"]["data"]
    try:
        return read_witness_file(cert).decode("ascii")
    except UnicodeDecodeError:
        witness = cert["witness"]
        what = "the generator's output" if "generated" in witness else f"witness file {witness['file']}"
        raise CertificateError(f"{cert['id']}: {what} isn't ASCII text")


def decompress(data: bytes, suffix: str, name: str) -> bytes:
    """Decompress gzip (.gz) or xz (.xz) data, refusing more than
    MAX_UNCOMPRESSED_BYTES."""
    decompressor = zlib.decompressobj(wbits=31) if suffix == ".gz" else lzma.LZMADecompressor()
    try:
        out = decompressor.decompress(data, MAX_UNCOMPRESSED_BYTES + 1)
    except (zlib.error, lzma.LZMAError) as e:
        raise CertificateError(f"{name}: can't decompress: {e}")
    complete = decompressor.eof
    if len(out) > MAX_UNCOMPRESSED_BYTES:
        raise CertificateError(f"{name}: more than {MAX_UNCOMPRESSED_BYTES} bytes uncompressed")
    if not complete or decompressor.unused_data:
        raise CertificateError(f"{name}: isn't a single complete {suffix} stream")
    return out


def read_symbols(cert: Mapping[str, Any], symbols: str, what: str) -> str:
    """Read a witness written one symbol per item, ignoring whitespace and
    case, and check that it only uses the given symbols."""
    text = "".join(read_witness_data(cert).split()).lower()
    if not set(text) <= set(symbols):
        raise CertificateError(f"{what} must use the symbols {symbols[0]} to {symbols[-1]}")
    return text


def read_coloring(cert: Mapping[str, Any], colors: int) -> str:
    """Read a coloring with the given number of colors, written in base 36:
    0 to 9, then a to z."""
    if cert["witness"].get("format") != "coloring":
        raise CertificateError("Witness must use format: coloring")
    if not 1 <= colors <= len(BASE36):
        raise CertificateError(f"Colorings can have at most {len(BASE36)} colors")
    return read_symbols(cert, BASE36[:colors], "Coloring")
