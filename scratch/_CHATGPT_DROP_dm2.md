# Q94 (dm2): Planning — `preΨ'_4` separability via Bezout

Target brick for the first nontrivial even case:

```lean
theorem preΨ'_four_isCoprime_derivative
    (W : WeierstrassCurve k) [W.IsElliptic] (h2 : (2 : k) ≠ 0) :
    IsCoprime (W.preΨ' 4) (Polynomial.derivative (W.preΨ' 4))
```

Here `W.preΨ' 4 = W.preΨ 4 = W.preΨ₄`, where

```text
preΨ₄ = 2X^6 + b₂X^5 + 5b₄X^4 + 10b₆X^3 + 10b₈X^2
        + (b₂b₈ - b₄b₆)X + (b₄b₈ - b₆^2).
```

This is a plan-only note; I did not dump the full Bezout cofactors yet.

## 1. Resultant / discriminant constant

Let

```text
f = preΨ₄,
f' = derivative_X preΨ₄,
Δ = -b₂^2 b₈ - 8 b₄^3 - 27 b₆^2 + 9 b₂ b₄ b₆,
bRel = b₂ b₆ - b₄^2 - 4 b₈.
```

The classical discriminant stated in the prompt is

```text
Disc(f) = -2^8 · Δ^5.
```

For a degree-`6` polynomial with leading coefficient `lc(f) = 2`, the convention is

```text
Disc(f) = (-1)^(6*5/2) * lc(f)^(-1) * Res(f, f')
        = - Res(f, f') / 2.
```

Therefore

```text
Res_X(preΨ₄, preΨ₄') = 2^9 · Δ^5 = 512 · Δ^5
```

modulo `bRel`.

Equivalently, the Bezout certificate should have the form

```text
A44 * preΨ₄ + B44 * preΨ₄' - 512 * Δ^5 - Q44 * bRel = 0
```

with all coefficients integral.

I sanity-checked this by a Sylvester/adjugate computation over `ZZ[b₂,b₄,b₆,b₈]`.  The exact resultant has `117` terms before reducing by `bRel`, and

```text
Res_X(preΨ₄, preΨ₄') - 512 * Δ^5 = Q44 * bRel
```

with a `b`-cofactor `Q44` having `98` terms.

The important Lean consequence is that no factor of `3` is needed.  Even though `preΨ₄'` has leading coefficient `12`, the final obstruction is only `2^9 · Δ^5`.  Hence the n=4 separability statement should need exactly `(2 : k) ≠ 0` plus `[W.IsElliptic]`.

A small reproducibility script for the constant/sign and size estimate is:

```python
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy.polys.domains import ZZ

b2,b4,b6,b8,x = sp.symbols('b2 b4 b6 b8 x')
K = ZZ.old_poly_ring(b2,b4,b6,b8)

def Ksym(a):
    return K.from_sympy(sp.sympify(a))

def to_sym(a):
    return K.to_sympy(a)

def sylvester_bezout_stats(f,g):
    m = sp.Poly(f,x).degree()
    n = sp.Poly(g,x).degree()
    N = m+n
    def coeff_desc(poly,deg):
        P = sp.Poly(poly,x)
        return [P.coeff_monomial(x**e) for e in range(deg,-1,-1)]
    cols = []
    for i in range(n):
        cols.append(coeff_desc(x**(n-1-i)*f,N-1))
    for j in range(m):
        cols.append(coeff_desc(x**(m-1-j)*g,N-1))
    M = DomainMatrix([[Ksym(cols[c][r]) for c in range(N)] for r in range(N)], (N,N), K)
    rhs = DomainMatrix([[Ksym(0)] for _ in range(N-1)] + [[Ksym(1)]], (N,1), K)
    xnum, xden = M.solve_den(rhs, method='charpoly')
    sol = [sp.expand(xnum.to_Matrix()[i,0]) for i in range(N)]
    A = sp.expand(sum(sol[i]*x**(n-1-i) for i in range(n)))
    B = sp.expand(sum(sol[n+j]*x**(m-1-j) for j in range(m)))
    R = to_sym(xden)
    assert sp.expand(A*f + B*g - R) == 0
    return A,B,R

f = 2*x**6 + b2*x**5 + 5*b4*x**4 + 10*b6*x**3 + 10*b8*x**2 + (b2*b8-b4*b6)*x + (b4*b8-b6**2)
g = sp.diff(f,x)
Delta = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6
bRel = b2*b6 - b4**2 - 4*b8

A,B,R = sylvester_bezout_stats(f,g)
assert sp.expand(R - sp.resultant(f,g,x)) == 0
Q,rem = sp.div(sp.expand(R - 2**9*Delta**5), bRel, b8)
assert rem == 0
assert sp.expand(A*f + B*g - 2**9*Delta**5 - Q*bRel) == 0

print('Res = 2^9 * Delta^5 mod bRel')
print('deg_x A <=', sp.Poly(A,x).degree(), 'terms(A)=', len(sp.Poly(A,x,b2,b4,b6,b8).terms()))
print('deg_x B <=', sp.Poly(B,x).degree(), 'terms(B)=', len(sp.Poly(B,x,b2,b4,b6,b8).terms()))
print('terms(R)=', len(sp.Poly(R,b2,b4,b6,b8).terms()))
print('terms(Q)=', len(sp.Poly(Q,b2,b4,b6,b8).terms()))
print('OK')
```

Output from the size probe:

```text
Res = 2^9 * Delta^5 mod bRel
deg_x A <= 4 terms(A)= 342
deg_x B <= 5 terms(B)= 425
terms(R)= 117
terms(Q)= 98
OK
```

## 2. Cofactor-size estimate

The Sylvester matrix size is `6 + 5 = 11`.

For the standard Sylvester Bezout shape

```text
A44 * f + B44 * f' = Res(f,f')
```

one can take

```text
deg_X A44 < deg_X f' = 5, so deg_X A44 ≤ 4,
deg_X B44 < deg_X f  = 6, so deg_X B44 ≤ 5.
```

The raw fraction-free Sylvester/adjugate solution I probed has:

```text
A44: 342 terms, total degree 15 in (X,b₂,b₄,b₆,b₈), deg_X 4
B44: 425 terms, total degree 16 in (X,b₂,b₄,b₆,b₈), deg_X 5
Q44:  98 terms, b-only, total degree 13
```

So the certificate is **moderate but not tiny**.  It is not smaller than the keystone `preΨ₄`-style ~250-term certificate if measured by total terms in `A+B`; it is around `342 + 425 + 98 = 865` printed terms for the raw Sylvester certificate.  But it is dramatically smaller than the Q47 `Ψ₃` vs `preΨ₄` certificate, and it should be mechanically manageable for Lean as a single `linear_combination` identity.

There may be a smaller syzygy-adjusted certificate because the derivative pair has extra structure.  For the first Lean attempt I would still use the raw Sylvester certificate unless the generated term is too slow for `ring_nf`.

## 3. Lean lemma shape

### Polynomial identity

Define `q94A44`, `q94B44`, and `q94Q44` by direct `C`/`X` lifting of the expanded integer expressions.

Example translation:

```text
-7*b2**3*b4*b6*x**4
  ↦ C ((-7 : R) * W.b₂ ^ 3 * W.b₄ * W.b₆) * X ^ 4
```

The identity should be oriented as:

```lean
import Mathlib

noncomputable section

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

-- To be filled by generated C/X-lifted integer expressions.
def q94A44 (W : WeierstrassCurve R) : R[X] := 0
def q94B44 (W : WeierstrassCurve R) : R[X] := 0
def q94Q44 (W : WeierstrassCurve R) : R[X] := 0

lemma q94_preΨ₄_derivative_bezout (W : WeierstrassCurve R) :
    q94A44 W * (W.preΨ 4) + q94B44 W * Polynomial.derivative (W.preΨ 4)
      = C ((512 : R) * W.Δ ^ 5) := by
  -- CAS identity:
  -- A44*preΨ₄ + B44*preΨ₄' - 512*Δ^5 - Q44*bRel = 0.
  -- Mathlib has `W.b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2`,
  -- while `bRel = W.b₂*W.b₆ - W.b₄^2 - 4*W.b₈`, so use `.symm`.
  linear_combination (norm := ring_nf [q94A44, q94B44, q94Q44,
      WeierstrassCurve.preΨ, WeierstrassCurve.Δ])
    q94Q44 W * ((congrArg (fun t : R => (C t : R[X])) W.b_relation).symm)

end WeierstrassCurve
```

If `W.preΨ 4` does not unfold conveniently through `WeierstrassCurve.preΨ`, add the local simp lemma that exposes the closed form of `preΨ₄`; the CAS identity is exactly for that closed form.

### Coprimality of `preΨ₄` with its derivative

Over a field, the right-hand side is a unit under `[W.IsElliptic]` and `(2 : k) ≠ 0`:

```text
(512 : k) * W.Δ^5 = (2 : k)^9 * W.Δ^5 ≠ 0.
```

`W.Δ` is nonzero because `WeierstrassCurve.isUnit_Δ` gives `IsUnit W.Δ`.

Skeleton:

```lean
namespace WeierstrassCurve

variable {k : Type*} [Field k]

lemma preΨ₄_isCoprime_derivative
    (W : WeierstrassCurve k) [W.IsElliptic] (h2 : (2 : k) ≠ 0) :
    IsCoprime (W.preΨ 4) (Polynomial.derivative (W.preΨ 4)) := by
  have hbez := q94_preΨ₄_derivative_bezout (W := W)
  have hΔ : W.Δ ≠ 0 := (WeierstrassCurve.isUnit_Δ (W := W)).ne_zero
  have h512 : (512 : k) ≠ 0 := by
    -- `512 = 2^9`; exact script can be made by `norm_num` plus `h2`, or by
    -- changing to `(2 : k)^9` and using `pow_ne_zero`.
    norm_num [show (2 : k) ≠ 0 from h2]
  have hscalar_ne : (512 : k) * W.Δ ^ 5 ≠ 0 := by
    exact mul_ne_zero h512 (pow_ne_zero 5 hΔ)
  have hscalar_unit : IsUnit ((512 : k) * W.Δ ^ 5) := by
    exact isUnit_of_ne_zero hscalar_ne
  -- Convert the Bezout identity with unit RHS into a Bezout identity with RHS `1`.
  -- Depending on local API, either use `IsCoprime`'s existential form directly,
  -- or a lemma saying `a*f + b*g` is a unit implies `IsCoprime f g`.
  obtain ⟨u, hu⟩ := hscalar_unit
  -- Schematic direct proof:
  -- refine ⟨q94A44 W * C ↑u⁻¹, q94B44 W * C ↑u⁻¹, ?_⟩
  -- calc
  --   (q94A44 W * C ↑u⁻¹) * W.preΨ 4
  --       + (q94B44 W * C ↑u⁻¹) * derivative (W.preΨ 4)
  --       = (q94A44 W * W.preΨ 4 + q94B44 W * derivative (W.preΨ 4)) * C ↑u⁻¹ := by ring
  --   _ = C ((512 : k) * W.Δ ^ 5) * C ↑u⁻¹ := by rw [hbez]
  --   _ = 1 := by simpa [hu]
  sorry

end WeierstrassCurve
```

A useful helper to avoid repeating the last block:

```lean
lemma isCoprime_of_linear_combination_isUnit
    {R : Type*} [CommRing R] {a b x y : R}
    (h : IsUnit (x * a + y * b)) : IsCoprime a b := by
  -- likely already in Mathlib under a similar name; otherwise prove by multiplying
  -- the linear combination by the inverse unit.
  sorry
```

Then the proof after `hbez` becomes only:

```lean
  exact isCoprime_of_linear_combination_isUnit
    (a := W.preΨ 4)
    (b := Polynomial.derivative (W.preΨ 4))
    (x := q94A44 W)
    (y := q94B44 W)
    (by simpa [hbez] using Polynomial.isUnit_C.mpr hscalar_unit)
```

The exact theorem name for `C` preserving units may differ; if it is inconvenient, use the explicit inverse construction above.

### Wrapper for `preΨ'_4`

Once the closed-form equality is available, the target wrapper should be trivial:

```lean
theorem preΨ'_four_isCoprime_derivative
    (W : WeierstrassCurve k) [W.IsElliptic] (h2 : (2 : k) ≠ 0) :
    IsCoprime (W.preΨ' 4) (Polynomial.derivative (W.preΨ' 4)) := by
  -- Expected to close by the local simp lemma `W.preΨ' 4 = W.preΨ 4`.
  simpa using preΨ₄_isCoprime_derivative (W := W) h2
```

## Risk / implementation notes

* The main identity is a single `linear_combination` over integers, so it fits the Q37/Q47 proof pattern.
* The constant is `512 * Δ^5`, not just `Δ^5`; this is harmless over a field with `(2 : k) ≠ 0`.
* No `(3 : k) ≠ 0` hypothesis should be needed.  This is a good regression check for the certificate.
* If `ring_nf` is slow with ~865 printed terms, try a syzygy-adjusted certificate or split the polynomial identity into a generated `bRel` certificate lemma plus a short wrapper.
* This n=4 case is a good testbed for the general resultant/Wronskian route because it proves the theorem without invoking the full induction machinery.
