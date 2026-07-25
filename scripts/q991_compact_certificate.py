#!/usr/bin/env python3
"""Q991 compact certificates built on the exact full-identity audit."""

from __future__ import annotations

import sympy as sp

# Importing executes all exact checks and exposes the audited expressions.
import q991_compute_hat_y as q

u, v, p, r = q.u, q.v, q.p, q.r
s, U, T, E, g = q.ss, q.UU, q.TT, q.EE, q.gg

# Polynomial numerator of w = x3-r after the hat and branch substitutions:
#     w = z / (u^2 s^2).
z = p**2*U**2 - u**2*s**2*T
assert sp.cancel(q.w3 - z/(u**2*s**2)) == 0

# Once the target X-coordinate has first been rewritten using the hat-X theorem,
# the remaining line defect has the compact coefficient qYline.
qYline = (
    (z-u**3*s**2)
    * (z-u**2*v*s**2)
    * (u**2*g*s**2-2*p**2*U**3)
)
assert sp.expand(q.line_coeff-qYline) == 0
assert sp.expand(q.line_num-qYline*E) == 0
assert sp.expand(q.line_den-2*p*u**3*s**3*z**2) == 0

# Compact hat-X defect.  The orientation is
#     target doubled X - phiX(source third X).
qX = u**4*s**6 - 4*z*(p**2*U**2 + u**2*U*(s**2+U*T))
assert sp.cancel(
    q.x_defect - E*qX/(4*p**2*u**2*s**2*z)
) == 0

# Full Y defect = line_defect + mu*x_defect.  On the reduced common
# denominator 8*p^3*u^3*s^3*z^2, its coefficient is the following compact sum.
qYfull = 4*p**2*qYline + u**2*z*g*qX
assert sp.expand(q.red_coeff-qYfull) == 0
assert sp.expand(q.red_num-qYfull*E) == 0
assert sp.expand(q.red_den-8*p**3*u**3*s**3*z**2) == 0

print()
print("## Compact structured certificate")
print()
print("Use")
print()
print("```text")
print("u = x1-r")
print("v = x2-r")
print("s = u-v")
print("U = u+v")
print("T = 3*r+U")
print("p = y1")
print("E = p^2-u^2*T")
print("g = s^2+2*U*T")
print("z = p^2*U^2-u^2*s^2*T")
print("```")
print()
print("The standard-addY full defect is exactly")
print()
print("```text")
print("qYfull * E / (8*p^3*u^3*s^3*z^2)")
print("```")
print()
print("where")
print()
print("```text")
print("qYline =")
print("  (z-u^3*s^2)")
print("  * (z-u^2*v*s^2)")
print("  * (u^2*g*s^2-2*p^2*U^3)")
print()
print("qX =")
print("  u^4*s^6")
print("  - 4*z*(p^2*U^2 + u^2*U*(s^2+U*T))")
print()
print("qYfull = 4*p^2*qYline + u^2*z*g*qX")
print("```")
print()
print("The decomposition verified is")
print()
print("```text")
print("full_Y_defect = line_defect + mu * X_defect")
print("mu = u*g/(2*p*s)")
print()
print("line_defect = qYline*E/(2*p*u^3*s^3*z^2)")
print("X_defect    = qX*E/(4*p^2*u^2*s^2*z)")
print("```")
print()
print("For Mathlib negAddY, or if the equality is normalized in the opposite")
print("orientation, negate qYline/qYfull as appropriate.")
