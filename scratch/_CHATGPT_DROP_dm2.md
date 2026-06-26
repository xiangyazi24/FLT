# Q818 (dm2): `preΨ'(4)` separability via a generated Bézout certificate

## Bottom line

For `n = 4`, I would **not** try to build a reusable resultant theory first.  The most direct Lean path is:

1. use Mathlib’s lemma

```lean
@[simp] lemma WeierstrassCurve.preΨ'_four : W.preΨ' 4 = W.preΨ₄
```

2. generate one explicit certificate

```lean
A₄(W) * W.preΨ₄ + B₄(W) * derivative W.preΨ₄
  = C ((2 : K)^9 * W.Δ ^ 5),
```

3. use `[W.IsElliptic]` to get `W.Δ ≠ 0`, and `(4 : K) ≠ 0` to get `(2 : K) ≠ 0`, and
4. scale the certificate by the inverse of the nonzero constant.

This proves

```lean
IsCoprime (W.preΨ' 4) (derivative (W.preΨ' 4))
```

without needing a general `Polynomial.resultant_ne_zero → IsCoprime` API.

The resultant identity is still useful as a CAS sanity check, but the Lean proof should consume the **Bézout identity**, not the resultant theorem.

---

## Step 1: exact Mathlib definition of `preΨ₄`

Mathlib defines:

```lean
noncomputable def WeierstrassCurve.preΨ₄ : R[X] :=
  2 * X ^ 6
    + C W.b₂ * X ^ 5
    + 5 * C W.b₄ * X ^ 4
    + 10 * C W.b₆ * X ^ 3
    + 10 * C W.b₈ * X ^ 2
    + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X
    + C (W.b₄ * W.b₈ - W.b₆ ^ 2)
```

and then

```lean
@[simp]
lemma WeierstrassCurve.preΨ'_four : W.preΨ' 4 = W.preΨ₄
```

So the target is really about `W.preΨ₄`.

Important: `preΨ₄` is written in terms of the `bᵢ`, but for the resultant formula you must substitute the actual Weierstrass definitions

```lean
b₂ = a₁^2 + 4 a₂
b₄ = 2 a₄ + a₁ a₃
b₆ = a₃^2 + 4 a₆
b₈ = a₁^2 a₆ + 4 a₂ a₆ - a₁ a₃ a₄ + a₂ a₃^2 - a₄^2
```

and

```lean
Δ = -b₂^2 b₈ - 8 b₄^3 - 27 b₆^2 + 9 b₂ b₄ b₆.
```

Do **not** compute the final certificate over independent variables `b₂,b₄,b₆,b₈`.  The simple formula

```text
Res(preΨ₄, preΨ₄') = 2^9 Δ^5
```

uses the Weierstrass relation among the `bᵢ`, especially

```lean
4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2.
```

If `b₂,b₄,b₆,b₈` are treated as algebraically independent, Sympy gives a huge unrelated resultant.

---

## Step 2: derivative of `preΨ₄`

The derivative is:

```lean
derivative W.preΨ₄ =
  12 * X ^ 5
    + C (5 * W.b₂) * X ^ 4
    + C (20 * W.b₄) * X ^ 3
    + C (30 * W.b₆) * X ^ 2
    + C (20 * W.b₈) * X
    + C (W.b₂ * W.b₈ - W.b₄ * W.b₆)
```

A small Lean lemma should prove this once and keep the generated certificate readable:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

lemma derivative_preΨ₄ :
    derivative W.preΨ₄ =
      12 * X ^ 5
        + C (5 * W.b₂) * X ^ 4
        + C (20 * W.b₄) * X ^ 3
        + C (30 * W.b₆) * X ^ 2
        + C (20 * W.b₈) * X
        + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) := by
  rw [preΨ₄]
  -- `ring_nf` usually succeeds here; if not, expand derivative simp lemmas first.
  ring_nf

end WeierstrassCurve
```

If `ring_nf` does not unfold enough in the local file, use:

```lean
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_X, derivative_C, map_ofNat, C_0, C_1]
  ring_nf
```

---

## Step 3: generate the Bézout cofactors by Sympy

The robust way is not `sp.gcdex` over the rational function field; that tends to create enormous rational cancellations.  Instead, build the multiplication map

```text
(A, B) ↦ A · f + B · f'
```

with

```text
deg A < 5,
deg B < 6,
```

where `f = preΨ₄`.  This is an `11 × 11` Sylvester-style matrix.  Solving this system fraction-free gives the adjugate-column Bézout certificate.

Use the actual `aᵢ` variables, not independent `bᵢ` variables.

```python
#!/usr/bin/env python3
import sympy as sp
from sympy.polys.matrices import DomainMatrix

# Polynomial variable and universal Weierstrass coefficients.
x = sp.Symbol("x")
a1, a2, a3, a4, a6 = sp.symbols("a1 a2 a3 a4 a6")

# Mathlib's b-invariants.
b2 = a1**2 + 4*a2
b4 = 2*a4 + a1*a3
b6 = a3**2 + 4*a6
b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2

Delta = sp.expand(-b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6)

# Mathlib's preΨ₄.
f = sp.expand(
    2*x**6
    + b2*x**5
    + 5*b4*x**4
    + 10*b6*x**3
    + 10*b8*x**2
    + (b2*b8 - b4*b6)*x
    + (b4*b8 - b6**2)
)
g = sp.diff(f, x)

# Expected resultant / certificate constant.
target = sp.expand(2**9 * Delta**5)

# Coefficient vector in ascending powers of x, length maxdeg+1.
def coeff_vec(poly, maxdeg):
    P = sp.Poly(sp.expand(poly), x)
    return [P.coeff_monomial(x**i) for i in range(maxdeg + 1)]

# Unknowns are coefficients of A, deg A < 5, and B, deg B < 6.
# The columns are coeff vectors of x^i*f and x^j*g.
cols = []
for i in range(5):
    cols.append(sp.Matrix(coeff_vec(x**i * f, 10)))
for j in range(6):
    cols.append(sp.Matrix(coeff_vec(x**j * g, 10)))

S = sp.Matrix.hstack(*cols)
rhs = sp.Matrix([1] + [0]*10)

# Work over ZZ[a1,a2,a3,a4,a6], not over a rational function field.
domain = sp.ZZ.poly_ring(a1, a2, a3, a4, a6)
Sdm = DomainMatrix.from_Matrix(S, domain=domain)
rhsdm = DomainMatrix.from_Matrix(rhs, (11, 1), domain=domain)

# solve_den returns sol, den with S * sol = den * rhs.
# The denominator should divide the resultant.  We scale to target = 2^9 * Delta^5.
sol_dm, den = Sdm.solve_den(rhsdm, method="charpoly")
sol_mat = sol_dm.to_Matrix()
den_expr = sp.factor(den.as_expr())

q = sp.cancel(target / den_expr)
q_num, q_den = sp.fraction(q)
assert q_den == 1, f"denominator did not divide target; den={den_expr}"
q = sp.expand(q_num)

sol = [sp.expand(q * sol_mat[i, 0]) for i in range(11)]

A = sp.expand(sum(sol[i] * x**i for i in range(5)))
B = sp.expand(sum(sol[5 + j] * x**j for j in range(6)))

check = sp.Poly(sp.expand(A*f + B*g - target), x)
assert check.is_zero, "Bézout identity failed"

print("degree A =", sp.Poly(A, x).degree())
print("degree B =", sp.Poly(B, x).degree())
print("den =", den_expr)
print("scaled by q =", sp.factor(q))
print("certificate OK")
```

If `solve_den(..., method="charpoly")` is slow, try the default method:

```python
sol_dm, den = Sdm.solve_den(rhsdm)
```

or explicitly use the adjugate/determinant path:

```python
adj, den = Sdm.adj_det()
sol_dm = adj.matmul(rhsdm)
```

The `solve_den` version is usually preferable because it may return a smaller denominator; the script then scales the certificate back up to the canonical target `2^9 * Δ^5`.

---

## Exporting Lean definitions

After the script computes `A` and `B`, generate Lean definitions.  The generated cofactors should be polynomials in `X` whose coefficients are expressions in `W.a₁,W.a₂,W.a₃,W.a₄,W.a₆`.

Here is a minimal printer skeleton:

```python
var_to_lean = {
    a1: "W.a₁",
    a2: "W.a₂",
    a3: "W.a₃",
    a4: "W.a₄",
    a6: "W.a₆",
}

def lean_expr(e):
    e = sp.expand(e)
    if e == 0:
        return "0"
    if e == 1:
        return "1"
    if e == -1:
        return "-1"
    if e in var_to_lean:
        return var_to_lean[e]
    if e.is_Integer:
        return str(int(e))
    if e.is_Add:
        return "(" + " + ".join(lean_expr(t) for t in e.as_ordered_terms()) + ")"
    if e.is_Mul:
        coeff, rest = e.as_coeff_Mul()
        if coeff == -1:
            return "(-" + lean_expr(rest) + ")"
        if coeff != 1:
            return "(" + str(int(coeff)) + " * " + lean_expr(rest) + ")"
        return "(" + " * ".join(lean_expr(t) for t in e.as_ordered_factors()) + ")"
    if e.is_Pow:
        base, exp = e.as_base_exp()
        assert exp.is_Integer and exp >= 0
        return "(" + lean_expr(base) + ") ^ " + str(int(exp))
    raise ValueError(f"unhandled expression: {e!r}")

def lean_poly(poly):
    P = sp.Poly(sp.expand(poly), x)
    terms = []
    for (deg,), coeff in sorted(P.terms(), reverse=False):
        if coeff == 0:
            continue
        c = "C (" + lean_expr(coeff) + ")"
        if deg == 0:
            terms.append(c)
        elif deg == 1:
            terms.append(c + " * X")
        else:
            terms.append(c + f" * X ^ {deg}")
    if not terms:
        return "0"
    return "\n    + ".join(terms)

with open("scratch/PrePsi4Certificate.lean", "w", encoding="utf-8") as out:
    out.write("import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic\n")
    out.write("import Mathlib.Tactic\n\n")
    out.write("open Polynomial\n\n")
    out.write("namespace WeierstrassCurve\n\n")
    out.write("noncomputable section\n\n")
    out.write("variable {K : Type*} [Field K]\n")
    out.write("variable (W : WeierstrassCurve K)\n\n")
    out.write("def preΨ₄BezoutA : K[X] :=\n    ")
    out.write(lean_poly(A))
    out.write("\n\n")
    out.write("def preΨ₄BezoutB : K[X] :=\n    ")
    out.write(lean_poly(B))
    out.write("\n\n")
    out.write("end\n\n")
    out.write("end WeierstrassCurve\n")
```

This printer is intentionally simple.  It will produce large expressions, but Lean accepts heavily parenthesized ring expressions.

---

## The generated Lean certificate theorem

After inserting the generated `preΨ₄BezoutA` and `preΨ₄BezoutB`, add:

```lean
namespace WeierstrassCurve

open Polynomial

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

lemma preΨ₄_bezout_certificate :
    W.preΨ₄BezoutA * W.preΨ₄
      + W.preΨ₄BezoutB * derivative W.preΨ₄
      = C ((2 : K) ^ 9 * W.Δ ^ 5) := by
  rw [preΨ₄BezoutA, preΨ₄BezoutB]
  rw [preΨ₄, derivative_preΨ₄]
  rw [Δ, b₂, b₄, b₆, b₈]
  ring_nf

end WeierstrassCurve
```

If this single `ring_nf` is too slow, generate a coefficientwise theorem instead:

```lean
  ext n
  fin_cases n using -- not literally; use the local coefficient automation pattern
```

The practical version is to generate eleven coefficient goals for degrees `0, ..., 10` and one generic high-degree zero case.  Each coefficient identity is just a commutative-ring identity in `a₁,a₂,a₃,a₄,a₆`, and `ring_nf` is much easier on those smaller goals than on the full polynomial identity.

But I would first try the single `ring_nf`; for this degree-6 certificate it may be acceptable.

---

## Final separability theorem for `preΨ'(4)`

Once the certificate theorem exists, the proof is short.

```lean
namespace WeierstrassCurve

open Polynomial

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

lemma preΨ'_four_isCoprime_derivative
    [W.IsElliptic] (h4 : (4 : K) ≠ 0) :
    IsCoprime (W.preΨ' 4) (derivative (W.preΨ' 4)) := by
  rw [preΨ'_four]

  have h2 : (2 : K) ≠ 0 := by
    intro h2zero
    apply h4
    have hfour : (4 : K) = (2 : K) * (2 : K) := by norm_num
    rw [hfour, h2zero, zero_mul]

  let c : K := (2 : K) ^ 9 * W.Δ ^ 5

  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (pow_ne_zero 9 h2)
      (pow_ne_zero 5 W.isUnit_Δ.ne_zero)

  have hbez := W.preΨ₄_bezout_certificate

  refine ⟨C c⁻¹ * W.preΨ₄BezoutA, C c⁻¹ * W.preΨ₄BezoutB, ?_⟩
  calc
    (C c⁻¹ * W.preΨ₄BezoutA) * W.preΨ₄
        + (C c⁻¹ * W.preΨ₄BezoutB) * derivative W.preΨ₄
        = C c⁻¹ * (W.preΨ₄BezoutA * W.preΨ₄
            + W.preΨ₄BezoutB * derivative W.preΨ₄) := by
          ring
    _ = C c⁻¹ * C c := by
          rw [hbez]
          rfl
    _ = 1 := by
          rw [← C_mul]
          simp [c, hc]

end WeierstrassCurve
```

This uses the definition of `IsCoprime` directly:

```lean
def IsCoprime (x y : R) : Prop :=
  ∃ a b, a * x + b * y = 1
```

So no resultant API is needed in the final Lean theorem.

---

## Why this handles characteristic `3`

Do not assume `derivative W.preΨ₄` has degree `5`.  In characteristic `3`, the leading term

```text
12 X^5
```

vanishes.  This is harmless for the Bézout-certificate proof: the identity

```lean
A * preΨ₄ + B * derivative preΨ₄ = C ((2 : K)^9 * Δ^5)
```

specializes correctly in every characteristic.  The hypotheses only need

```lean
(4 : K) ≠ 0
```

and `[W.IsElliptic]`.  In characteristic `3`, `(4 : K) = 1`, so the theorem should still apply.

This is another reason to prefer a direct certificate over a proof that depends on the default `natDegree` of the derivative.

---

## Sanity checks to run in CAS

Before exporting Lean, run two checks.

First, check the short Weierstrass specialization `a₁=a₂=a₃=0`, `a₄=A`, `a₆=B`:

```python
A0, B0 = sp.symbols("A0 B0")
short = {
    a1: 0,
    a2: 0,
    a3: 0,
    a4: A0,
    a6: B0,
}
res_short = sp.factor(sp.resultant(f.subs(short), g.subs(short), x))
Delta_short = sp.factor(Delta.subs(short))
assert sp.factor(res_short - 2**9 * Delta_short**5) == 0
```

This should reproduce

```text
Res = 2^9 · Δ^5.
```

Second, after producing `A` and `B`, test several small integer specializations with nonsingular discriminant:

```python
tests = [
    {a1:0, a2:0, a3:0, a4:-1, a6:1},
    {a1:1, a2:0, a3:1, a4:-1, a6:2},
    {a1:2, a2:-1, a3:1, a4:3, a6:-2},
]
for t in tests:
    lhs = sp.Poly(sp.expand((A*f + B*g - target).subs(t)), x)
    assert lhs.is_zero, t
```

These are not proof steps, but they catch wrong matrix orientation and sign errors before Lean sees the certificate.

---

## Practical recommendation

Generate and check exactly one file containing:

```lean
def preΨ₄BezoutA : K[X] := ...
def preΨ₄BezoutB : K[X] := ...
lemma derivative_preΨ₄ : ...
lemma preΨ₄_bezout_certificate : ...
lemma preΨ'_four_isCoprime_derivative : ...
```

The only large part is the two generated cofactor definitions.  The mathematical proof is then just:

```text
Bézout certificate gives a nonzero constant in the ideal.
A nonzero constant is a unit in K[X].
Therefore preΨ₄ and derivative preΨ₄ are coprime.
preΨ'(4) = preΨ₄.
```

This is much lighter than formalizing the full resultant formula, and it avoids the derivative-degree pitfalls in characteristic `3`.
