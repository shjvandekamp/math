"""Small positive and deliberately broken certificates, independent of search code."""

from dataclasses import replace
import unittest

from verify_cards import (
    Card, Certificate, Hint, InvalidCertificate, MATRICES, SHAPE,
    SHAPE_ORIENTATIONS, check_card, normalize, parse_text, transform,
    verify_certificate, winning_witness,
)


# Two six-cell terminal cards and a two-threat predecessor, transcribed as data
# from compact cards 0, 1, 2.  No reference implementation is imported.
TERMINAL0 = Card(1, (1, 1), ((0, 1), (0, 2), (0, 3), (0, 4), (1, 0)),
                 ((0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1)), None, ())
TERMINAL1 = Card(1, (1, 0), ((0, 1), (0, 2), (0, 3), (0, 4), (1, 1)),
                 TERMINAL0.support, None, ())
PREDECESSOR = Card(2, (1, 1), ((0, 1), (0, 2), (0, 3), (0, 4), (0, 5)),
                   ((1, 0), (1, 2), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1)),
                   Hint(0, 0, 0, 1),
                   (((1, 0), Hint(0, 0, 0, 1)), ((1, 2), Hint(1, 0))))
CARDS = (TERMINAL0, TERMINAL1, PREDECESSOR)


class CardVerifierTests(unittest.TestCase):
    def assert_rejected(self, code, cards, index=2):
        with self.assertRaises(InvalidCertificate) as raised:
            check_card(cards, index)
        self.assertEqual(raised.exception.code, code)

    def test_exact_snaky_and_d4(self):
        self.assertEqual(len(SHAPE), 6)
        self.assertEqual(len(SHAPE_ORIENTATIONS), 8)
        from_hints = {normalize(transform(SHAPE, Hint(0, k))) for k in range(8)}
        self.assertEqual(from_hints, set(SHAPE_ORIENTATIONS))
        for k in range(8):
            points = transform(SHAPE, Hint(0, k, -17, 26))
            self.assertEqual(frozenset(winning_witness(points)), points)
        self.assertIsNone(winning_witness(frozenset((x, 0) for x in range(6))))
        self.assertIsNone(winning_witness(frozenset(SHAPE[:-1])))

    def test_symmetry_closure_and_injectivity(self):
        self.assertEqual(len(set(MATRICES)), 8)
        for a, b, c, d in MATRICES:
            self.assertEqual(abs(a * d - b * c), 1)
            for e, f, g, h in MATRICES:
                self.assertIn((a * e + b * g, a * f + b * h,
                               c * e + d * g, c * f + d * h), MATRICES)

    def test_positive_cards_and_exhaustive_inside_replies(self):
        self.assertTrue(check_card(CARDS, 0).terminal)
        self.assertTrue(check_card(CARDS, 1).terminal)
        checked = check_card(CARDS, 2)
        self.assertFalse(checked.terminal)
        self.assertEqual(checked.dependencies, (0, 1))
        self.assertEqual(checked.inside_replies, 2)

    def test_missing_response(self):
        changed = replace(PREDECESSOR, responses=PREDECESSOR.responses[:-1])
        self.assert_rejected("missing-response", CARDS[:2] + (changed,))

    def test_missing_outside_response(self):
        self.assert_rejected("missing-outside-response",
                             CARDS[:2] + (replace(PREDECESSOR, outside=None),))

    def test_reply_cannot_leave_white_in_child_support(self):
        changed = replace(PREDECESSOR, responses=(((1, 0), Hint(1, 0)),
                                                   PREDECESSOR.responses[1]))
        self.assert_rejected("white-collision", CARDS[:2] + (changed,))

    def test_bad_requirement(self):
        changed = replace(TERMINAL0, required=TERMINAL0.required + ((100, 100),))
        self.assert_rejected("requirements", (changed, TERMINAL1, PREDECESSOR))

    def test_bad_support_including_outside_class(self):
        changed = replace(TERMINAL0, support=TERMINAL0.support + ((100, 100),))
        self.assert_rejected("support", (changed, TERMINAL1, PREDECESSOR))

    def test_pivot_outside_support(self):
        changed = replace(PREDECESSOR, pivot=(100, 100))
        self.assert_rejected("pivot", CARDS[:2] + (changed,))

    def test_bad_symmetry(self):
        changed = replace(PREDECESSOR, outside=Hint(0, 8))
        self.assert_rejected("orientation", CARDS[:2] + (changed,))

    def test_unknown_target(self):
        changed = replace(PREDECESSOR, outside=Hint(99, 0))
        self.assert_rejected("reference", CARDS[:2] + (changed,))

    def test_bad_heights(self):
        changed = replace(TERMINAL0, height=2)
        self.assert_rejected("height-descent", (changed, TERMINAL1, PREDECESSOR))
        self.assert_rejected("height", (replace(TERMINAL0, height=0),), 0)
        self.assert_rejected("terminal-shape", CARDS[:2] + (replace(PREDECESSOR, height=1),))

    def test_malformed_terminal(self):
        malformed = replace(TERMINAL0, required=tuple((x, 0) for x in range(5)),
                            pivot=(5, 0), support=tuple((x, 0) for x in range(6)))
        self.assert_rejected("terminal-shape", (malformed,), 0)

    def test_duplicate_reply_uses_first_entry(self):
        bad = ((1, 0), Hint(1, 0))
        bad_first = replace(PREDECESSOR, responses=(bad,) + PREDECESSOR.responses)
        self.assert_rejected("white-collision", CARDS[:2] + (bad_first,))
        good_first = replace(PREDECESSOR, responses=PREDECESSOR.responses + (bad,))
        self.assertEqual(check_card(CARDS[:2] + (good_first,), 2).duplicate_response_keys, 1)

    def test_extra_black_stones_and_pivot_already_owned_are_allowed(self):
        # A need not be contained in S, and p need not be a fresh black stone.
        card = Card(1, SHAPE[0], SHAPE, (SHAPE[0],), None, ())
        self.assertTrue(check_card((card,), 0).terminal)

    def test_terminal_has_no_response_obligation(self):
        card = replace(TERMINAL0, outside=Hint(999, 0),
                       responses=(((100, 100), Hint(999, 0)),))
        self.assertTrue(check_card((card,), 0).terminal)

    def test_parser_exact_record(self):
        text = ("snaky-cards-txt-v1 17 17 0 0 -2 3\n"
                "1 1 1 5 0 1 0 2 0 3 0 4 1 0 6 0 1 0 2 0 3 0 4 1 0 1 1 -1 0\n")
        result = parse_text(text)
        self.assertEqual(result, Certificate(17, 17, Hint(0, 0, -2, 3), (TERMINAL0,)))

    def test_parser_rejects_malformed_input(self):
        inputs = (
            ("format", "nonsense"),
            ("integer", "snaky-cards-txt-v1 17 17 x 0 0 0"),
            ("orientation", "snaky-cards-txt-v1 17 17 0 8 0 0"),
            ("negative-natural", "snaky-cards-txt-v1 17 17 -1 0 0 0"),
            ("empty", "snaky-cards-txt-v1 17 17 0 0 0 0"),
            ("truncated", "snaky-cards-txt-v1 17 17 0 0 0 0 1"),
            ("pass-sentinel", "snaky-cards-txt-v1 17 17 0 0 0 0 1 0 0 0 1 0 0 -2 0"),
        )
        for code, text in inputs:
            with self.subTest(code=code):
                with self.assertRaises(InvalidCertificate) as raised:
                    parse_text(text)
                self.assertEqual(raised.exception.code, code)

    def test_root_must_start_empty(self):
        with self.assertRaises(InvalidCertificate) as raised:
            verify_certificate(Certificate(17, 17, Hint(2, 0), CARDS))
        self.assertEqual(raised.exception.code, "root-requirements")

    def test_reused_hint_keeps_each_parent_obligation(self):
        # Card 2 already uses these same child hints successfully. Card 3
        # must still check its own ownership, support and current White reply.
        cases = (
            ("white-collision", replace(PREDECESSOR,
                responses=(((1, 0), Hint(1, 0)), PREDECESSOR.responses[1]))),
            ("requirements", replace(PREDECESSOR, required=PREDECESSOR.required[:-1])),
            ("support", replace(PREDECESSOR,
                support=tuple(p for p in PREDECESSOR.support if p != (1, 2)))),
        )
        for code, changed in cases:
            with self.subTest(code=code):
                with self.assertRaises(InvalidCertificate) as raised:
                    verify_certificate(Certificate(17, 17, Hint(2, 0), CARDS + (changed,)))
                self.assertEqual(raised.exception.code, code)

    def test_geometry_does_not_leak_between_certificates(self):
        with self.assertRaises(InvalidCertificate) as first:
            verify_certificate(Certificate(17, 17, Hint(2, 0), CARDS))
        self.assertEqual(first.exception.code, "root-requirements")
        changed = replace(TERMINAL0, required=TERMINAL0.required + ((100, 100),))
        with self.assertRaises(InvalidCertificate) as second:
            verify_certificate(Certificate(17, 17, Hint(2, 0),
                                           (changed, TERMINAL1, PREDECESSOR)))
        self.assertEqual(second.exception.code, "requirements")

    def test_parser_keeps_ascii_integer_grammar(self):
        for token in ("+1", "1_0", "٠", "1.0", "--1"):
            with self.subTest(token=token):
                with self.assertRaises(InvalidCertificate) as raised:
                    parse_text("snaky-cards-txt-v1 17 17 " + token)
                self.assertEqual(raised.exception.code, "integer")


if __name__ == "__main__":
    unittest.main()
