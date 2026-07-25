## Q996 exact scaling result

- SymPy version: `1.14.0`
- primitive normalization unit: `1`
- primitive numerator terms: `96`
- primitive numerator SHA-256: `c3ad57a2988eae2073eb889ceda40edb635bd5cac2db7cb8bf34b43253ea8219`

### Exact denominators

- primitive denominator: `y1**2*(-r + x1)*(-A - 2*r**2 - 2*r*x1 + x1**2)**2*(A**2 + 6*A*x1**2 - 4*r*y1**2 + 9*x1**4 - 8*x1*y1**2)`
- whole-together denominator: `4*y1**2*(-r + x1)*(-A - 2*r**2 - 2*r*x1 + x1**2)**2*(A**2 + 6*A*x1**2 - 4*r*y1**2 + 9*x1**4 - 8*x1*y1**2)`
- left-side denominator: `4*y1**2*(A**2 + 6*A*x1**2 - 4*r*y1**2 + 9*x1**4 - 8*x1*y1**2)`
- right-side denominator: `4*y1**2*(-r + x1)*(-A - 2*r**2 - 2*r*x1 + x1**2)**2`
- side-product denominator: `16*y1**4*(-r + x1)*(-A - 2*r**2 - 2*r*x1 + x1**2)**2*(A**2 + 6*A*x1**2 - 4*r*y1**2 + 9*x1**4 - 8*x1*y1**2)`
- summand denominator 1: `4*y1**2`
- summand denominator 2: `A**2 + 6*A*x1**2 - 4*r*y1**2 + 9*x1**4 - 8*x1*y1**2`
- summand denominator 3: `4*y1**2*(-A - 2*r**2 - 2*r*x1 + x1**2)**2`
- summand denominator 4: `-r + x1`
- summand-product denominator: `16*y1**4*(-r + x1)*(-A - 2*r**2 - 2*r*x1 + x1**2)**2*(A**2 + 6*A*x1**2 - 4*r*y1**2 + 9*x1**4 - 8*x1*y1**2)`

### Exact scaling factors relative to Q971 N

- k_whole = `4`
- k_side = `16*y1**2`
- k_summand = `16*y1**2`

### Verification

- whole_num = k_whole * N: `True`
- whole_den = k_whole * primitive_den: `True`
- side_product_num = k_side * N: `True`
- side_product_den = k_side * primitive_den: `True`
- summand_product_num = k_summand * N: `True`
- summand_product_den = k_summand * primitive_den: `True`
- every scaled numerator equals (k*C)*hcurve1 + (k*C)*htors: `True`

### Compact Q971 coefficient

```text
z  = y1^2
t  = 3*r^2 + A
d  = x1 - r
e  = d^2 - t
u  = 3*x1^2 + A
m  = x1*d + t
p  = 3*m^2 + (A - 5*t)*d^2
h  = 2*x1 + r
q  = 2*t - d*h
F0 = x1^3 + A*x1 - r^3 - A*r
C  = d*h*p^2 + e^2*(u^2*q - 12*t*(x1+r)*(z+F0))
```

### Exact scaled coefficients

- whole-together coefficient factorization: `8*(A + 3*r**2)*(A**4 + 6*A**3*r**2 + 6*A**3*x1**2 + 6*A**2*r**4 + 6*A**2*r**3*x1 + 36*A**2*r**2*x1**2 - 6*A**2*r*x1**3 - 6*A**2*r*y1**2 + 12*A**2*x1**4 - 6*A**2*x1*y1**2 + 36*A*r**4*x1**2 + 36*A*r**3*x1**3 - 24*A*r**3*y1**2 + 54*A*r**2*x1**4 - 48*A*r**2*x1*y1**2 - 36*A*r*x1**5 - 12*A*r*x1**2*y1**2 + 18*A*x1**6 + 12*A*x1**3*y1**2 - 24*r**5*y1**2 + 54*r**4*x1**4 - 72*r**4*x1*y1**2 + 54*r**3*x1**5 - 48*r**3*x1**2*y1**2 + 24*r**2*x1**3*y1**2 - 54*r*x1**7 + 18*r*x1**4*y1**2 + 27*x1**8 - 6*x1**5*y1**2)`
- side-product coefficient factorization: `32*y1**2*(A + 3*r**2)*(A**4 + 6*A**3*r**2 + 6*A**3*x1**2 + 6*A**2*r**4 + 6*A**2*r**3*x1 + 36*A**2*r**2*x1**2 - 6*A**2*r*x1**3 - 6*A**2*r*y1**2 + 12*A**2*x1**4 - 6*A**2*x1*y1**2 + 36*A*r**4*x1**2 + 36*A*r**3*x1**3 - 24*A*r**3*y1**2 + 54*A*r**2*x1**4 - 48*A*r**2*x1*y1**2 - 36*A*r*x1**5 - 12*A*r*x1**2*y1**2 + 18*A*x1**6 + 12*A*x1**3*y1**2 - 24*r**5*y1**2 + 54*r**4*x1**4 - 72*r**4*x1*y1**2 + 54*r**3*x1**5 - 48*r**3*x1**2*y1**2 + 24*r**2*x1**3*y1**2 - 54*r*x1**7 + 18*r*x1**4*y1**2 + 27*x1**8 - 6*x1**5*y1**2)`
- summand-product coefficient factorization: `32*y1**2*(A + 3*r**2)*(A**4 + 6*A**3*r**2 + 6*A**3*x1**2 + 6*A**2*r**4 + 6*A**2*r**3*x1 + 36*A**2*r**2*x1**2 - 6*A**2*r*x1**3 - 6*A**2*r*y1**2 + 12*A**2*x1**4 - 6*A**2*x1*y1**2 + 36*A*r**4*x1**2 + 36*A*r**3*x1**3 - 24*A*r**3*y1**2 + 54*A*r**2*x1**4 - 48*A*r**2*x1*y1**2 - 36*A*r*x1**5 - 12*A*r*x1**2*y1**2 + 18*A*x1**6 + 12*A*x1**3*y1**2 - 24*r**5*y1**2 + 54*r**4*x1**4 - 72*r**4*x1*y1**2 + 54*r**3*x1**5 - 48*r**3*x1**2*y1**2 + 24*r**2*x1**3*y1**2 - 54*r*x1**7 + 18*r*x1**4*y1**2 + 27*x1**8 - 6*x1**5*y1**2)`
