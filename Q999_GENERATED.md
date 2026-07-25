# Q999 exact B-free Route A audit

- SymPy version: `1.14.0`
- full rational hat X identity: `verified`
- branch-product certificate for hm: `verified`
- hE, hA, and hB polynomial certificates: `verified`
- compact identity `u^2*N0 = cE*E + cM*m`: `verified`
- primitive `u^2*N0` terms: `217`
- primitive `u^2*N0` SHA-256: `8e536a6be815157a8e9a1726bf8639edb3d316a83c52728ea24f13966802bdd2`

## Exact scaling factors relative to u^2*N0

- k_whole = `1`
- k_side = `(x1 - x2)**2`
- k_summand = `(x1 - x2)**2`

## Exact denominators

- primitive: `-4*y1**2*(x1 - x2)**2*(r*x1**2 - 2*r*x1*x2 + r*x2**2 + x1**3 - x1**2*x2 - x1*x2**2 + x2**3 - y1**2 + 2*y1*y2 - y2**2)`
- whole together: `-4*y1**2*(x1 - x2)**2*(r*x1**2 - 2*r*x1*x2 + r*x2**2 + x1**3 - x1**2*x2 - x1*x2**2 + x2**3 - y1**2 + 2*y1*y2 - y2**2)`
- left side: `4*y1**2*(x1 - x2)**2`
- right side: `-(x1 - x2)**2*(r*x1**2 - 2*r*x1*x2 + r*x2**2 + x1**3 - x1**2*x2 - x1*x2**2 + x2**3 - y1**2 + 2*y1*y2 - y2**2)`
- side product: `-4*y1**2*(x1 - x2)**4*(r*x1**2 - 2*r*x1*x2 + r*x2**2 + x1**3 - x1**2*x2 - x1*x2**2 + x2**3 - y1**2 + 2*y1*y2 - y2**2)`
- summand 1: `4*y1**2*(x1 - x2)**2`
- summand 2: `1`
- summand 3: `(x1 - x2)**2`
- summand 4: `-r*x1**2 + 2*r*x1*x2 - r*x2**2 - x1**3 + x1**2*x2 + x1*x2**2 - x2**3 + y1**2 - 2*y1*y2 + y2**2`
- summand product: `-4*y1**2*(x1 - x2)**4*(r*x1**2 - 2*r*x1*x2 + r*x2**2 + x1**3 - x1**2*x2 - x1*x2**2 + x2**3 - y1**2 + 2*y1*y2 - y2**2)`

## Compact coefficients

```text
u = x1-r; v = x2-r; s = x1-x2; U = u+v; T = x1+x2+r
d = y1-y2; z = d^2-s^2*T; g = s^2+2*U*T
K = u*d+U*y1
cE = u^2*s^6 - 4*z*(y1^2*U^2 + u^2*U*(s^2+U*T))
cM = K*(4*z*y1^2-u^2*s^4)
```

## Candidate field_simp-scaled coefficients

- side-scaled cE multiplier: `(x1 - x2)**2`
- side-scaled cM multiplier: `(x1 - x2)**2`
- summand-scaled cE multiplier: `(x1 - x2)**2`
- summand-scaled cM multiplier: `(x1 - x2)**2`
