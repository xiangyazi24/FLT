Q991 exact SymPy result
========================
SymPy version: 1.14.0
pure ring identity after only hat + branch: False
reduced numerator terms: 197
compact qYfull expanded terms: 140
raw/reduced multiplier: 1
verified: red_num = qYfull * E
verified: raw_num = raw_multiplier * qYfull * E

u = x1-r; v = x2-r; s = u-v; U = u+v; T = 3*r+U; p = y1
E = p^2-u^2*T
g = s^2+2*U*T
z = p^2*U^2-u^2*s^2*T
qYline = (z-u^3*s^2)*(z-u^2*v*s^2)*(u^2*g*s^2-2*p^2*U^3)
qX = u^4*s^6-4*z*(p^2*U^2+u^2*U*(s^2+U*T))
qYfull = 4*p^2*qYline+u^2*z*g*qX
red_den = 8*p^3*u^3*s^3*z^2

E_original = C1 + H - (x1-r)*G
standard-addY reduced-numerator coefficients:
  hcurve1: qYfull_original
  hcurve2: 0
  htors:   qYfull_original
  hat:    -(x1-r)*qYfull_original
For negAddY or the opposite defect orientation, negate all coefficients.
