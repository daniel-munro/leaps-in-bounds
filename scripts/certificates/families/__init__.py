"""The families of constants that accept certificates, one module per family
(or pair of related families), matching the Lean statements in
formal/LeapsInBounds/Statements/.

Each module defines FAMILIES, mapping family IDs to how to check their
certificates: the Lean statement of a bound, and a witness checker.
"""

from typing import Any, Mapping

from ..errors import CertificateError
from ..family import Family
from ..generator import GeneratorOutput, generated_witness
from . import (
    busy_beaver,
    cage,
    cap_set,
    chromatic_number_space,
    circle_in_square,
    circle_in_triangle,
    debruijn_newman,
    degree_diameter,
    disk_covering,
    folding,
    golomb,
    heilbronn,
    isosceles_set,
    kissing_number,
    lebesgue_cover,
    line_arrangement,
    moving_sofa,
    multicolor_ramsey,
    no_three_in_line,
    ramsey,
    rectilinear_crossing,
    schur,
    snake_in_the_box,
    sorting_network,
    square_packing,
    superpermutation,
    tammes,
    van_der_waerden,
)


FAMILIES: dict[str, Family] = {
    **ramsey.FAMILIES,
    **van_der_waerden.FAMILIES,
    **cage.FAMILIES,
    **degree_diameter.FAMILIES,
    **superpermutation.FAMILIES,
    **kissing_number.FAMILIES,
    **square_packing.FAMILIES,
    **circle_in_triangle.FAMILIES,
    **circle_in_square.FAMILIES,
    **schur.FAMILIES,
    **multicolor_ramsey.FAMILIES,
    **golomb.FAMILIES,
    **sorting_network.FAMILIES,
    **snake_in_the_box.FAMILIES,
    **cap_set.FAMILIES,
    **no_three_in_line.FAMILIES,
    **isosceles_set.FAMILIES,
    **line_arrangement.FAMILIES,
    **rectilinear_crossing.FAMILIES,
    **chromatic_number_space.FAMILIES,
    **busy_beaver.FAMILIES,
    **folding.FAMILIES,
    **disk_covering.FAMILIES,
    **debruijn_newman.FAMILIES,
    **tammes.FAMILIES,
    **heilbronn.FAMILIES,
    **moving_sofa.FAMILIES,
    **lebesgue_cover.FAMILIES,
}


def get_family(constant_id: str) -> tuple[Family, dict[str, int]]:
    for family in FAMILIES.values():
        match = family.id_pattern.fullmatch(constant_id)
        if match:
            return family, {k: int(v) for k, v in match.groupdict().items()}
    raise CertificateError(f"No certificate family supports constant {constant_id}")


def check_witness(cert: Mapping[str, Any]) -> list[str]:
    """Verify a witness certificate's evidence, returning any warnings: things
    worth knowing that don't make it fail."""
    family, params = get_family(cert["constant"])
    if family.witness_bound is not None and cert["bound"] != family.witness_bound:
        raise CertificateError(f"Witnesses for {cert['constant']} can only certify {family.witness_bound} bounds")
    if cert["witness"].get("format") != "generator":
        family.check_witness(params, cert["bound"], cert["value"], cert)
        return []
    with GeneratorOutput(cert) as output:
        try:
            family.check_witness(params, cert["bound"], cert["value"], generated_witness(cert, output))
            return output.finish()
        except CertificateError as e:
            # If the generator failed, that's the error to report. A warning,
            # such as a generator printing something different from what was
            # submitted, may explain the failure.
            message = output.failed() or str(e)
            raise CertificateError("".join([message, *(f"\n  Also: {w}" for w in output.warnings())]))
