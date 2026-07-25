#!/usr/bin/env python3
"""Probe cancellation and exact factorization of the verified Q974 certificate."""

from __future__ import annotations

import contextlib
import io
import sys

import sympy as sp

sys.path.insert(0, "scripts")
with contextlib.redirect_stdout(io.StringIO()):
    import q974_compute_nonhat_x as q

cancelled = sp.cancel(q.diff)
num_cancel, den_cancel = sp.fraction(cancelled)
num_cancel = sp.expand(num_cancel)
den_cancel = sp.factor(den_cancel)

print("together numerator terms:", q.term_count(q.num))
print("cancelled numerator terms:", q.term_count(num_cancel))
print("same numerator exactly:", sp.expand(q.num - num_cancel) == 0)
print("same denominator exactly:", sp.expand(q.den - den_cancel) == 0)
print("rational cross-check:", sp.expand(q.num * den_cancel - num_cancel * q.den) == 0)
print("gcd(num_raw, den_raw):", sp.factor(sp.gcd(q.num_raw, q.den_raw)))
print()

for name, coeff in (("c1", q.c1), ("c2", q.c2), ("c3", q.c3)):
    print(f"## {name}")
    content, factors = sp.factor_list(coeff)
    print("content:", content)
    print("factor count:", len(factors))
    for factor, exponent in factors:
        print("exponent:", exponent)
        print("expanded terms:", q.term_count(factor))
        print("factor:", sp.sstr(factor, order="lex"))
    print("full factor:", sp.sstr(sp.factor(coeff), order="lex"))
    print()
