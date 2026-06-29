# Q: FLT N12 nonaxis factor-identity residual

## Verdict

I do **not** think the compact residual has a small counterexample. More strongly: after a sign normalization, each of its four factor-identity branches produces a rational point on the already-known hard boundary curve

\[
F: Y^2=X^3+2X^2-3X=X(X-1)(X+3),
\]

with

\[
X\in\{t^2,\ -t^2,\ 3t^2,\ -3t^2\},
\qquad t=\frac mA\in\mathbf Q^*.
\]

Using the rational point classification for `F`, this forces `t^2=1`; substituting back into the relevant branch then forces `m=n` or `m=-n`, contradicting the opposite-parity hypothesis. So the compact residual is contradictory, but not by an obviously finite congruence argument. It has simply repackaged the same elliptic-curve boundary.

Thus: no explicit `(m,n,a,c)` counterexample satisfying all hypotheses; the compact residual is strong enough **provided the shifted curve point boundary is available**.

## 1. Normalize the residual

Let

\[
D=m^2-n^2=(m-n)(m+n),\qquad P=mn.
\]

The two signed halves of `NonAxisFactorIdentityResidual` can be normalized as follows.

If `a*c = m*n`, set

\[
A=a,\qquad C=c.
\]

If `a*c = -(m*n)`, set

\[
A=a,\qquad C=-c.
\]

Then always

\[
A C = m n,
\]

and one of the following four normalized identities holds:

\[
\begin{array}{ll}
\text{B1:} & D=(A-C)(3A-C),\\[2mm]
\text{B2:} & D=-(A+C)(3A+C),\\[2mm]
\text{B3:} & D=(A-C)(A-3C),\\[2mm]
\text{B4:} & D=-(A+C)(A+3C).
\end{array}
\]

Since `m*n ≠ 0`, also `A ≠ 0` and `C ≠ 0`.

Lean-friendly normalization predicate:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Normalized four-branch factor identity after absorbing the sign of `a*c = ±m*n`. -/
def NormalizedNonAxisFactorIdentity (m n A C : ℤ) : Prop :=
  A * C = m * n ∧
    ((m - n) * (m + n) = (A - C) * (3 * A - C) ∨
     (m - n) * (m + n) = -((A + C) * (3 * A + C)) ∨
     (m - n) * (m + n) = (A - C) * (A - 3 * C) ∨
     (m - n) * (m + n) = -((A + C) * (A + 3 * C)))

/-- The compact residual sign-normalizes to `A*C=m*n` and one of four branches. -/
theorem NonAxisFactorIdentityResidual.normalize
    {m n a c : ℤ}
    (h : NonAxisFactorIdentityResidual m n a c) :
    ∃ A C : ℤ, NormalizedNonAxisFactorIdentity m n A C := by
  -- first signed half: use A=a, C=c
  -- second signed half: use A=a, C=-c
  sorry

end MazurProof.RationalPointsN12
```

## 2. Branch-to-elliptic-curve transformation

Work over `ℚ`. From `A*C=m*n` with `A ≠ 0`, define

\[
t=\frac mA,\qquad r=\frac CA,\qquad q=t^2.
\]

Since `A*C=m*n`, one has `n=C/t` in `ℚ`. Each branch becomes a quadratic equation in `r`; completing the discriminant gives a point on `F`.

### Branch B1

From

\[
m^2-n^2=(A-C)(3A-C)
\]

one derives

\[
\big((q+1)r-2q\big)^2=q(q-1)(q+3).
\]

Thus

\[
(X,Y)=\left(q,\ (q+1)r-2q\right)
\]

lies on `F`.

### Branch B2

From

\[
m^2-n^2=-(A+C)(3A+C)
\]

one derives

\[
\big((q-1)r+2q\big)^2=q(3-q)(q+1).
\]

Thus

\[
(X,Y)=\left(-q,\ (q-1)r+2q\right)
\]

lies on `F`, because

\[
(-q)(-q-1)(-q+3)=q(q+1)(3-q).
\]

### Branch B3

From

\[
m^2-n^2=(A-C)(A-3C)
\]

one derives

\[
\big((1+3q)r-2q\big)^2=q(3q-1)(q+1).
\]

Thus

\[
(X,Y)=\left(3q,\ 3\big((1+3q)r-2q\big)\right)
\]

lies on `F`.

### Branch B4

From

\[
m^2-n^2=-(A+C)(A+3C)
\]

one derives

\[
\big((3q-1)r+2q\big)^2=q(1-q)(3q+1).
\]

Thus

\[
(X,Y)=\left(-3q,\ 3\big((3q-1)r+2q\big)\right)
\]

lies on `F`.

Lean-friendly branch lemmas:

```lean
namespace MazurProof.RationalPointsN12

/-- Shifted curve equation. -/
def F_N12_AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

/-- Branch B1 gives a point on `F` with `X=(m/A)^2`. -/
theorem branch_B1_to_F
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C)) :
    ∃ Y : ℚ,
      F_N12_AffineEquation (((m : ℚ) / A) ^ 2) Y := by
  sorry

/-- Branch B2 gives a point on `F` with `X=-((m/A)^2)`. -/
theorem branch_B2_to_F
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB2 : (m - n) * (m + n) = -((A + C) * (3 * A + C))) :
    ∃ Y : ℚ,
      F_N12_AffineEquation (-(((m : ℚ) / A) ^ 2)) Y := by
  sorry

/-- Branch B3 gives a point on `F` with `X=3*(m/A)^2`. -/
theorem branch_B3_to_F
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB3 : (m - n) * (m + n) = (A - C) * (A - 3 * C)) :
    ∃ Y : ℚ,
      F_N12_AffineEquation (3 * (((m : ℚ) / A) ^ 2)) Y := by
  sorry

/-- Branch B4 gives a point on `F` with `X=-3*(m/A)^2`. -/
theorem branch_B4_to_F
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB4 : (m - n) * (m + n) = -((A + C) * (A + 3 * C))) :
    ∃ Y : ℚ,
      F_N12_AffineEquation (-3 * (((m : ℚ) / A) ^ 2)) Y := by
  sorry

end MazurProof.RationalPointsN12
```

The proofs are `field_simp` plus `ring`, using `A ≠ 0`, `m ≠ 0`, and `A*C=m*n`.

## 3. Use the hard `F` boundary

The only hard theorem needed is the shifted curve x-coordinate boundary:

```lean
namespace MazurProof.RationalPointsN12

/-- Hard arithmetic boundary from the future 2-isogeny/torsion proof. -/
theorem F_N12_shifted_x_cases
    {X Y : ℚ}
    (hF : F_N12_AffineEquation X Y) :
    X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3 := by
  sorry

end MazurProof.RationalPointsN12
```

Together with elementary rational-square lemmas:

```lean
namespace MazurProof.RationalPointsN12

/-- `3` is not a rational square. -/
theorem rat_sq_ne_three (t : ℚ) : t ^ 2 ≠ 3 := by
  sorry

/-- `1/3` is not a rational square. -/
theorem rat_sq_ne_one_div_three (t : ℚ) : t ^ 2 ≠ (1 / 3 : ℚ) := by
  sorry

end MazurProof.RationalPointsN12
```

The boundary forces `q=t^2=1` in every branch:

* B1 gives `X=q`; the point list allows only `q=1` among nonzero rational squares.
* B2 gives `X=-q`; the point list allows `q=1` or `q=3`, and `q=3` is impossible for a rational square.
* B3 gives `X=3q`; the point list allows `q=1` or `q=1/3`, and `q=1/3` is impossible for a rational square.
* B4 gives `X=-3q`; the point list allows `q=1` or `q=1/3`, and `q=1/3` is impossible for a rational square.

So in all branches:

\[
\left(\frac mA\right)^2=1.
\]

Over integers this gives `m = A` or `m = -A`. Since `A*C=m*n`, also `n = C` or `n = -C` with the same sign.

Substituting into the branch identity gives:

| branch | forced relation |
|---:|---|
| B1 | `A = C`, hence `m = n` |
| B2 | `A = -C`, hence `m = -n` |
| B3 | `A = C`, hence `m = n` |
| B4 | `A = -C`, hence `m = -n` |

Either `m=n` or `m=-n` contradicts opposite parity.

Lean-level final theorem:

```lean
namespace MazurProof.RationalPointsN12

/-- The compact non-axis factor-identity residual is contradictory, assuming the
shifted curve x-coordinate boundary. -/
theorem no_NonAxisFactorIdentityResidual_of_F_boundary
    (hFbd : ∀ {X Y : ℚ},
      F_N12_AffineEquation X Y →
        X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
    {m n a c : ℤ}
    (hmn0 : m * n ≠ 0)
    (hcop : Int.gcd m n = 1)
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
            (m % 2 = 1 ∧ n % 2 = 0))
    (hres : NonAxisFactorIdentityResidual m n a c) :
    False := by
  -- 1. normalize hres to A,C with A*C=m*n and one of B1..B4;
  -- 2. branch_to_F gives an F-point with X in {q,-q,3q,-3q}, q=(m/A)^2;
  -- 3. hFbd plus rational-square lemmas force q=1;
  -- 4. q=1 plus A*C=m*n gives m=±A and n=±C;
  -- 5. the branch identity forces m=n or m=-n;
  -- 6. contradict hpar.
  sorry

/-- Bridge-level contradiction matching the current reduction shape. -/
theorem no_nonaxis_bridge_residual_of_F_boundary
    (hFbd : ∀ {X Y : ℚ},
      F_N12_AffineEquation X Y →
        X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3) :
    ¬ ∃ m n a c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      ((m % 2 = 0 ∧ n % 2 = 1) ∨
       (m % 2 = 1 ∧ n % 2 = 0)) ∧
      NonAxisFactorIdentityResidual m n a c := by
  rintro ⟨m, n, a, c, hmn0, hcop, hpar, hres⟩
  exact no_NonAxisFactorIdentityResidual_of_F_boundary
    hFbd hmn0 hcop hpar hres

end MazurProof.RationalPointsN12
```

The `hcop` hypothesis is not essential for the branch-to-curve contradiction, but keeping it in the theorem is useful because it matches the current bridge output.

## 4. Is a finite congruence proof likely?

Not from the compact residual alone. The normalized branches naturally produce rational points on `F`; the obstruction is exactly that `F(Q)` has only

\[
X\in\{-3,-1,0,1,3\}.
\]

That is the same hard arithmetic boundary already isolated in Q2179/Q2208. So the shortest honest proof route is:

```text
compact residual
  -> normalized branch B1/B2/B3/B4
  -> rational point on F with X = q, -q, 3q, or -3q
  -> F_N12_shifted_x_cases
  -> q = 1
  -> m = ±n
  -> parity contradiction.
```

This is Lean-friendly and avoids reintroducing `b,r,s`, but it does not avoid the elliptic-curve theorem.

## 5. Should the stronger signed residual retain extra data?

For contradiction **via the `F` boundary**, no extra data is needed: the compact residual is enough.

If the goal is instead to search for a more elementary proof before invoking the elliptic-curve boundary, then the compact residual has forgotten useful structure. In that case, retain the stronger signed data explicitly:

```lean
namespace MazurProof.RationalPointsN12

/-- Stronger signed residual retaining the quartic square and coprime factor split. -/
structure NonAxisSignedResidualData (m n : ℤ) : Prop where
  hmn0 : m * n ≠ 0
  hcop_mn : Int.gcd m n = 1
  hparity : (m % 2 = 0 ∧ n % 2 = 1) ∨
             (m % 2 = 1 ∧ n % 2 = 0)
  b r s a c : ℤ
  hquartic :
    b ^ 2 = m ^ 4 + 8 * m ^ 3 * n + 2 * m ^ 2 * n ^ 2
      - 8 * m * n ^ 3 + n ^ 4
  hrs : r * s = 3 * m ^ 2 * n ^ 2
  hrs_coprime : Int.gcd r s = 1
  hac : a * c = m * n ∨ a * c = -(m * n)
  hfactor : NonAxisFactorIdentityResidual m n a c
  -- Add the actual signed equations identifying r,s with the relevant half-factors
  -- before the square/three-square split. Those are the data lost by the compact form.

end MazurProof.RationalPointsN12
```

A replacement theorem for that stronger interface would be:

```lean
namespace MazurProof.RationalPointsN12

/-- Stronger signed residual contradiction. This may admit extra local arguments,
but the compact residual already suffices once `F_N12_shifted_x_cases` is known. -/
theorem no_NonAxisSignedResidualData_of_F_boundary
    (hFbd : ∀ {X Y : ℚ},
      F_N12_AffineEquation X Y →
        X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
    {m n : ℤ}
    (h : NonAxisSignedResidualData m n) :
    False := by
  exact no_NonAxisFactorIdentityResidual_of_F_boundary
    hFbd h.hmn0 h.hcop_mn h.hparity h.hfactor

end MazurProof.RationalPointsN12
```

So the actionable recommendation is: keep the compact residual if the N12 file is allowed to depend on the `F` rational-point boundary. Restore `b,r,s` only if you want to attempt a separate elementary/local proof that does not use the elliptic-curve classification.
