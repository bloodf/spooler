"""What Spoolman itself does with a write, for the stand-in Spoolmans of the tests, so they refuse
what the real one refuses and change what it changes (read from Spoolman's source, v0.21 to v0.27):

- extra: before 0.22.0 a PATCH replaces the whole map; from 0.22.0 it is merged key by key
  (commit 28f6f8e); from 0.26.0 a null value removes a key (ae3208a), before it is a 422.
- filament colour: the request body's multi_color_hexes and multi_color_direction are checked
  together (api/v1/filament.py model_validator), on a PATCH too.
- spool weights: Spoolman keeps used_weight; remaining is base - used, the base being the initial
  weight or else the filament's, so a PATCH of remaining_weight null fails (base - None) with a 500,
  one with no base at all is refused, and a new initial_weight moves remaining.
"""

import io
import json
import re
import urllib.error


def refuse(code: int, message: str) -> urllib.error.HTTPError:
    return urllib.error.HTTPError("spoolman", code, "refused", {}, io.BytesIO(json.dumps({"message": message}).encode()))


def version_tuple(text: str) -> tuple | None:
    found = re.match(r"v?(\d+)\.(\d+)\.(\d+)", str(text or ""))
    return tuple(int(x) for x in found.groups()) if found else None


def merge_extra(current: dict, sent: dict, version: str) -> dict:
    """The extra map after a PATCH that sent `sent`, on that Spoolman version."""
    v = version_tuple(version) or (99, 0, 0)
    if any(value is None for value in sent.values()) and v < (0, 26, 0):
        raise refuse(422, "extra values must be strings")
    if v < (0, 22, 0):
        return dict(sent)
    out = dict(current)
    for key, value in sent.items():
        if value is None:
            out.pop(key, None)
        else:
            out[key] = value
    return out


def check_filament_body(body: dict) -> None:
    """Spoolman's colour check of a filament request body."""
    hexes, direction = body.get("multi_color_hexes"), body.get("multi_color_direction")
    if hexes and not direction:
        raise refuse(422, "Multi-color filament must have multi_color_direction set")
    if direction and not hexes:
        raise refuse(422, "Single-color filament must not have multi_color_direction set")
    if hexes and len(str(hexes).split(",")) < 2:
        raise refuse(422, "Multi-color filament must have at least 2 colors")
    if hexes and body.get("color_hex"):
        raise refuse(422, "Cannot specify both color_hex and multi_color_hexes")


def patch_filament(filament: dict, body: dict, version: str) -> None:
    check_filament_body(body)
    body = dict(body)
    if "extra" in body:
        filament["extra"] = merge_extra(filament.get("extra") or {}, body.pop("extra"), version)
    filament.update(body)


def patch_spool(spool: dict, body: dict, version: str) -> None:
    """Spool fields in Spoolman's order: initial first, then remaining as used = base - remaining,
    where the base is the initial weight, else the filament's weight."""
    body = dict(body)
    if "extra" in body:
        spool["extra"] = merge_extra(spool.get("extra") or {}, body.pop("extra"), version)
    base = lambda: spool.get("initial_weight") if spool.get("initial_weight") is not None else (spool.get("filament") or {}).get("weight")  # noqa: E731
    used = spool["used_weight"] if spool.get("used_weight") is not None else (base() or 0) - (spool.get("remaining_weight") or 0)
    if "initial_weight" in body:
        spool["initial_weight"] = body.pop("initial_weight")
    if "remaining_weight" in body:
        left = body.pop("remaining_weight")
        if left is None:
            raise refuse(500, "unsupported operand type(s) for -")
        if base() is None:
            raise refuse(400, "remaining_weight can only be used if initial_weight or the filament weight is set")
        used = max(base() - left, 0)
    spool.update(body)
    spool["used_weight"] = used
    spool["remaining_weight"] = None if base() is None else max(base() - used, 0)
