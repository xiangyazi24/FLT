#!/usr/bin/env python3
"""Probe exact cancellation and factorization of the verified Q974 certificate."""

from __future__ import annotations

import contextlib
import io
import sys

import sympy as sp

sys.path.insert(0, "scripts")
with contextlib.redirect_stdout(io.StringIO()):
    import q974_compute_nonhat_x as q

print("raw together numerator terms:", q.term_count(q.raw_num))
print("reduced numerator terms:", q.term_count(q.num))
print("raw multiplier:", sp.sstr(q.raw_multiplier, order="lex"))
print("raw numerator check:", sp.expand(q.raw_num - q.raw_multiplier*q.num) == 0)
print("rational cross-check:", sp.expand(q.raw_num*q.den - q.num*q.raw_den) == 0)
print("gcd(raw_num_expr, raw_den_expr):", sp.factor(sp.gcd(q.raw_num_expr, q.raw_den_expr)))
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
