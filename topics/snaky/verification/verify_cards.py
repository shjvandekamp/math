#!/usr/bin/env python3
"""Independently check snaky-cards-txt-v1 certificates; Python standard library only.

Semantics are taken from Snaky/{Game,Cards,CardsSound,Bounded}.lean, not
from the reference Python checker or certificate-construction code.  This is
an executable audit, not a replacement for a proof assistant's kernel.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import sys
import time
from typing import Iterable


Point = tuple[int, int]
SHAPE: tuple[Point, ...] = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))
_INTEGER_TOKEN = re.compile(r"-?[0-9]+")

# These indices are part of the compact format, not the orientation-generation
# algorithm used below to recognize a terminal Snaky placement.
MATRICES = (
    (1, 0, 0, 1), (-1, 0, 0, 1), (0, -1, 1, 0), (0, 1, 1, 0),
    (-1, 0, 0, -1), (1, 0, 0, -1), (0, 1, -1, 0), (0, -1, -1, 0),
)


class InvalidCertificate(ValueError):
    """A failed obligation, with a stable short code for negative controls."""

    def __init__(self, code: str, detail: str):
        self.code = code
        super().__init__(f"{code}: {detail}")


def require(condition: bool, code: str, detail: str) -> None:
    if not condition:
        raise InvalidCertificate(code, detail)


@dataclass(frozen=True)
class Hint:
    card: int
    orientation: int
    dx: int = 0
    dy: int = 0


@dataclass(frozen=True)
class Card:
    height: int
    pivot: Point
    required: tuple[Point, ...]
    support: tuple[Point, ...]
    outside: Hint | None
    responses: tuple[tuple[Point, Hint], ...]


@dataclass(frozen=True)
class Certificate:
    rows: int
    cols: int
    root: Hint
    cards: tuple[Card, ...]


class _Reader:
    def __init__(self, values: list[int]):
        self.values = values
        self.position = 0

    def next(self, label: str) -> int:
        require(self.position < len(self.values), "truncated", f"missing {label}")
        value = self.values[self.position]
        self.position += 1
        return value

    def natural(self, label: str) -> int:
        value = self.next(label)
        require(value >= 0, "negative-natural", label)
        return value

    def point(self, label: str) -> Point:
        return self.next(label + " x"), self.next(label + " y")

    def points(self, label: str) -> tuple[Point, ...]:
        count = self.natural(label + " count")
        require(2 * count <= len(self.values) - self.position,
                "truncated", label + " points exceed remaining tokens")
        return tuple(self.point(label) for _ in range(count))

    def hint(self, label: str, card: int | None = None) -> Hint:
        index = self.natural(label + " card") if card is None else card
        require(index >= 0, "negative-natural", label + " card")
        orientation = self.natural(label + " orientation")
        require(orientation < 8, "orientation", label + " index must be in 0..7")
        dx, dy = self.point(label + " translation")
        return Hint(index, orientation, dx, dy)


def parse_text(text: str) -> Certificate:
    """Strict whitespace-token parser; no silent defaults or integer coercions.

    Compared with Lean's permissive untrusted parser, this accepts a subset of
    syntax: exact tag, integer tokens, nonnegative natural fields, orientation
    indices 0..7, only -1 for an absent pass, and no truncated last record.
    On this accepted syntax both parsers produce the same mathematical data.
    """
    tokens = text.split()
    require(bool(tokens) and tokens[0] == "snaky-cards-txt-v1", "format", "wrong format tag")
    values = []
    for position, token in enumerate(tokens[1:], 1):
        if _INTEGER_TOKEN.fullmatch(token) is None:
            raise InvalidCertificate("integer", f"invalid integer token {position}: {token!r}")
        values.append(int(token))
    reader = _Reader(values)
    rows, cols = reader.natural("rows"), reader.natural("columns")
    root = reader.hint("root")
    cards = []
    while reader.position < len(values):
        label = f"card {len(cards)}"
        height = reader.natural(label + " height")
        pivot = reader.point(label + " pivot")
        required = reader.points(label + " requirements")
        support = reader.points(label + " support")
        outside_index = reader.next(label + " outside response")
        require(outside_index >= -1, "pass-sentinel", label + " absent pass must be -1")
        outside = None if outside_index == -1 else reader.hint(label + " outside", outside_index)
        count = reader.natural(label + " reply count")
        require(6 * count <= len(values) - reader.position,
                "truncated", label + " replies exceed remaining tokens")
        responses = tuple((reader.point(label + " reply"), reader.hint(label + " reply"))
                          for _ in range(count))
        cards.append(Card(height, pivot, required, support, outside, responses))
    require(bool(cards), "empty", "no cards")
    return Certificate(rows, cols, root, tuple(cards))


def normalize(points: Iterable[Point]) -> tuple[Point, ...]:
    points = tuple(points)
    x0 = min(x for x, _ in points)
    y0 = min(y for _, y in points)
    return tuple(sorted((x - x0, y - y0) for x, y in points))


def _shape_orientations() -> tuple[tuple[Point, ...], ...]:
    """Generate D4 by reflection and quarter-turns, independently of hint indices."""
    result = set()
    for reflection in (1, -1):
        points = tuple((x, reflection * y) for x, y in SHAPE)
        for _ in range(4):
            result.add(normalize(points))
            points = tuple((-y, x) for x, y in points)
    return tuple(sorted(result))


SHAPE_ORIENTATIONS = _shape_orientations()


def winning_witness(black: frozenset[Point]) -> tuple[Point, ...] | None:
    """Return six actual cells witnessing a translated D4 Snaky, if one exists."""
    if len(black) < 6:
        return None
    for shape in SHAPE_ORIENTATIONS:
        ax, ay = shape[0]
        for bx, by in sorted(black):
            dx, dy = bx - ax, by - ay
            cells = tuple((x + dx, y + dy) for x, y in shape)
            if all(point in black for point in cells):
                return cells
    return None


def transform(points: Iterable[Point], hint: Hint) -> frozenset[Point]:
    require(0 <= hint.orientation < 8, "orientation", "index must be in 0..7")
    a, b, c, d = MATRICES[hint.orientation]
    return frozenset((a * x + b * y + hint.dx, c * x + d * y + hint.dy)
                     for x, y in points)


@dataclass(frozen=True)
class CardCheck:
    terminal: bool
    dependencies: tuple[int, ...]
    inside_replies: int
    ignored_response_entries: int
    duplicate_response_keys: int


def _hint_geometry(cards: tuple[Card, ...], hint: Hint):
    target = cards[hint.card]
    return transform(target.required, hint), transform(target.support, hint)


def _check_card(cards: tuple[Card, ...], index: int, geometry) -> CardCheck:
    """Check one local implication, with all finite and outside reply classes.

    The whole-certificate caller must check every card.  Requirements and support
    are membership predicates; duplicates in their lists are harmless.  Duplicate
    reply keys use the first entry, matching Lean's List.lookup.
    """
    card = cards[index]
    prefix = f"card {index}"
    require(card.height >= 1, "height", prefix + " height must be positive")
    support = frozenset(card.support)
    black = frozenset(card.required) | {card.pivot}
    require(card.pivot in support, "pivot", prefix + " pivot is outside support")

    if winning_witness(black) is not None:
        # Just as in cardOK, no White response is needed after a terminal move.
        return CardCheck(True, (), 0, len(card.responses), 0)
    require(card.height > 1, "terminal-shape", prefix + " height 1 does not complete Snaky")

    dependencies = set()

    def check_hint(hint: Hint, white: Point | None) -> None:
        context = prefix + (" outside reply" if white is None else f" reply {white}")
        require(0 <= hint.card < len(cards), "reference", context + " has no target card")
        target = cards[hint.card]
        require(1 <= target.height < card.height, "height-descent",
                context + f" target height {target.height} is not below {card.height}")
        need, region = geometry(hint)
        missing = need - black
        require(not missing, "requirements", context + f" requires unowned cells {sorted(missing)}")
        escaped = region - support
        require(not escaped, "support", context + f" escapes support at {sorted(escaped)}")
        require(white is None or white not in region, "white-collision",
                context + " leaves the White reply in the child's protected support")
        dependencies.add(hint.card)

    require(card.outside is not None, "missing-outside-response", prefix + " lacks its pass hint")
    check_hint(card.outside, None)

    # Do not make a dict directly: last-wins would disagree with Lean's lookup.
    responses = {}
    duplicates = 0
    for white, hint in card.responses:
        if white in responses:
            duplicates += 1
        else:
            responses[white] = hint
    replies = support - black
    for white in sorted(replies):
        require(white in responses, "missing-response", prefix + f" lacks reply {white}")
        check_hint(responses[white], white)
    ignored = len(card.responses) - len(replies)
    return CardCheck(False, tuple(sorted(dependencies)), len(replies), ignored, duplicates)


def check_card(cards: tuple[Card, ...], index: int) -> CardCheck:
    """Check one card independently, without sharing state with other certificates."""
    return _check_card(cards, index, lambda hint: _hint_geometry(cards, hint))


def verify_certificate(certificate: Certificate, max_root_height: int | None = None) -> dict:
    """Check every card, then the empty-board root and finite-board free-cell budget."""
    cards = certificate.cards
    require(bool(cards), "empty", "no cards")
    # Cache geometry only. Height, ownership, support and the current White
    # collision are still checked at every hint use. The closure owns this
    # immutable certificate, so entries cannot leak into another verification.
    @lru_cache(maxsize=512)
    def geometry(hint: Hint):
        return _hint_geometry(cards, hint)

    checks = [_check_card(cards, index, geometry) for index in range(len(cards))]
    hint = certificate.root
    require(0 <= hint.card < len(cards), "root-reference", "root card does not exist")
    root = cards[hint.card]
    require(not root.required, "root-requirements", "root does not start with empty Black ownership")
    region = transform(root.support, hint)
    rows, cols = certificate.rows, certificate.cols
    require(rows > 0 and cols > 0, "board", "board dimensions must be positive")
    outside_board = sorted((x, y) for x, y in region if not (0 <= x < cols and 0 <= y < rows))
    require(not outside_board, "root-support", f"root support escapes board: {outside_board}")
    require(2 * root.height <= rows * cols, "free-cells",
            "board cannot support the soundness invariant 2 * root height <= area")
    if max_root_height is not None:
        require(root.height <= max_root_height, "root-height",
                f"root height {root.height} exceeds requested bound {max_root_height}")

    # Audit the existing hint graph; this does not select alternative moves/hints.
    depths = [0] * len(cards)
    for index in sorted(range(len(cards)), key=lambda i: cards[i].height):
        children = checks[index].dependencies
        depths[index] = 1 + max((depths[child] for child in children), default=0)
        require(depths[index] <= cards[index].height, "hint-depth",
                f"card {index} depth exceeds its declared height")
    reachable = set()
    pending = [hint.card]
    while pending:
        index = pending.pop()
        if index not in reachable:
            reachable.add(index)
            pending.extend(checks[index].dependencies)
    xs, ys = zip(*region)
    return {
        "status": "verified",
        "game": "Snaky maker-breaker; Black first; six-cell D4 placements",
        "shape": [list(point) for point in SHAPE],
        "shape_orientation_count": len(SHAPE_ORIENTATIONS),
        "rows": rows,
        "cols": cols,
        "cards_checked": len(cards),
        "terminal_cards": sum(check.terminal for check in checks),
        "inside_reply_checks": sum(check.inside_replies for check in checks),
        "outside_reply_checks": sum(not check.terminal for check in checks),
        "ignored_response_entries": sum(check.ignored_response_entries for check in checks),
        "duplicate_response_keys": sum(check.duplicate_response_keys for check in checks),
        "root_index": hint.card,
        "root_height_black_moves": root.height,
        "root_hint_graph_depth": depths[hint.card],
        "reachable_cards": len(reachable),
        "root_support_cells": len(region),
        "root_support_bounds_xy": [min(xs), max(xs), min(ys), max(ys)],
        "root_inside_reply_classes": checks[hint.card].inside_replies,
        "root_board_cells_outside_support": rows * cols - len(region),
        "free_cell_budget_lhs": 2 * root.height,
        "board_cells": rows * cols,
        "max_card_height": max(card.height for card in cards),
        "optimality_claimed": False,
        "proof_assistant_kernel_checked_by_this_run": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--json", action="store_true", help="emit a machine-readable audit")
    parser.add_argument("--max-root-height", type=int,
                        help="also require the declared root bound to be at most this value")
    args = parser.parse_args(argv)
    started = time.perf_counter()
    try:
        data = args.certificate.read_bytes()
        certificate = parse_text(data.decode("ascii"))
        result = verify_certificate(certificate, args.max_root_height)
        result.update({
            "certificate_path": str(args.certificate),
            "certificate_sha256": hashlib.sha256(data).hexdigest(),
            "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "python_version": sys.version.split()[0],
            "elapsed_seconds": round(time.perf_counter() - started, 6),
        })
    except (InvalidCertificate, OSError, UnicodeError, ValueError) as error:
        if args.json:
            print(json.dumps({"status": "rejected", "error": str(error)}, indent=2))
        else:
            print(f"REJECTED: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"VERIFIED: {result['cards_checked']} cards, {result['inside_reply_checks']} inside "
              f"and {result['outside_reply_checks']} outside response checks; "
              f"Black wins on {result['rows']}x{result['cols']} within "
              f"{result['root_height_black_moves']} Black moves. "
              "Computational audit, not a new optimality result.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
