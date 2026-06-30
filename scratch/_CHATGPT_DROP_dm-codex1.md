# Q2355 (dm-codex1): roadmap for `EisensteinQuarticSquareClassification`

## Bottom line

The remaining theorem

```lean
def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2
```

is best treated as a finite rational-points computation for the genus-one quartic

\[
  C : y^2 = x^4 - x^2 + 1.
\]

The exact rational affine statement needed is

\[
  C(\mathbb Q)_{\mathrm{aff}}
  = \{(0,1),(0,-1),(1,1),(1,-1),(-1,1),(-1,-1)\}.
\]

Equivalently, the only rational `x`-coordinates on the affine quartic are

\[
  x = 0, \quad x^2 = 1.
\]

The homogeneous integer theorem follows immediately by taking, when `n ≠ 0`,

\[
  x = m/n, \qquad y = c/n^2.
\]

Then `x = 0` gives `m = 0`, and `x^2 = 1` gives `m^2 = n^2`.  The branch `n = 0` is one of the allowed conclusions.

The most Lean-friendly hard theorem to isolate is therefore **not** the original homogeneous integer statement, but the rational point theorem for `C` or, better, the finite affine point theorem for the birational elliptic curve below.

## 1. Exact classical theorem/source/name

I would **not** label the Lean theorem as “Ljunggren 1942” without qualification.

Ljunggren’s 1942 paper usually cited in this neighborhood is

> W. Ljunggren, *Zur Theorie der Gleichung* `x^2 + 1 = D y^4`, Avh. Norske Vid. Akad. Oslo I. 1942, no. 5, 27 pp.

That is a related quartic-Diophantine source and may be usable after an elementary factorization/descent reduction, but its headline theorem is **not literally** the homogeneous classification

\[
  z^2 = x^4 - x^2 y^2 + y^4.
\]

The exact theorem needed here is better named in the development as one of the following:

* `RatQuarticEisenstein_points`: finite rational points on `y^2 = x^4 - x^2 + 1`.
* `EisensteinQuarticCurve_rational_x`: rational `x`-coordinate classification, `x = 0 ∨ x^2 = 1`.
* `RatE_affine_points`: finite rational points on the Weierstrass model
  \[
    E : Y^2 = (X - 1)(X^2 - 4).
  \]

A modern proof route is the standard genus-one quartic-to-elliptic-curve transformation plus a rank-zero / torsion computation for `E`.  The finite point set is small enough that all downstream Lean work should be algebraic case splitting once this single elliptic-curve theorem is available.

## 2. Recommended proof routes ranked by Lean formalization cost

### Route A: assume/prove rational quartic point theorem directly, then denominator-clear

**Formalization cost:** lowest inside the current file; honest only if the rational point theorem is proved elsewhere.

Hard imported theorem:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- Affine rational quartic. -/
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- Stronger finite-point theorem; includes the `y` signs. -/
def RatQuarticEisensteinPointClassification : Prop :=
  ∀ {x y : ℚ},
    RatQuarticEisenstein x y →
      (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
      (x = 1 ∧ (y = 1 ∨ y = -1)) ∨
      (x = -1 ∧ (y = 1 ∨ y = -1))

/-- Minimal theorem actually needed by the integer classification. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ},
    RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1

end MazurProof.RationalPointsN12
```

Then prove the current integer theorem by rationalizing `m/n` when `n ≠ 0`.  This is the shortest route to close the current file, but it hides the real arithmetic in the rational point theorem.

### Route B: birational elliptic curve + finite `E(ℚ)` point set

**Formalization cost:** recommended.  The hard theorem becomes an exact finite point set on a single Weierstrass equation.  Everything else is `field_simp`, `ring`, and finite case analysis.

Target elliptic curve:

\[
  E : Y^2 = (X - 1)(X^2 - 4)
    = X^3 - X^2 - 4X + 4.
\]

Affine rational point set:

\[
  E(\mathbb Q)_{\mathrm{aff}}
  = \{(-2,0),(1,0),(2,0),(0,2),(0,-2),(4,6),(4,-6)\}.
\]

Projectively, add the point at infinity `O`.  The group is

\[
  E(\mathbb Q) \cong \mathbb Z/2\mathbb Z \times \mathbb Z/4\mathbb Z.
\]

For example, `(0,2)` has double `(2,0)`, and `(4,6)` also has double `(2,0)`.

This route is ideal because the map from the quartic to `E` is very explicit and the current theorem only needs `x = 0 ∨ x^2 = 1`, not the full inverse map.

### Route C: fully formalize the rank-zero computation by 2-descent

**Formalization cost:** high, but still more localized than a general Mordell-Weil library.

Use the translated curve

\[
  E' : V^2 = U(U+1)(U+4), \qquad U = X - 2.
\]

Then prove:

1. `E'` has full rational 2-torsion at `U = 0, -1, -4`.
2. The discriminant is supported only at `2` and `3`.
3. The 2-Selmer group has size `4`.
4. Therefore `rank E'(ℚ) = 0`.
5. Torsion is exactly `ℤ/2ℤ × ℤ/4ℤ`, with affine points
   \[
     (-4,0),(-1,0),(0,0),(-2,2),(-2,-2),(2,6),(2,-6).
   \]
6. Translate back by `X = U + 2` to get the point list on `E`.

This is a good standalone file if the project wants no external arithmetic facts.  It is still a nontrivial formalization project because mathlib does not currently make this a one-line theorem.

### Route D: elementary infinite descent / Eisenstein integers / Ljunggren-style reduction

**Formalization cost:** high to very high.

The identity

\[
  m^4 - m^2 n^2 + n^4 = (m^2 + \omega n^2)(m^2 + \omega^2 n^2)
\]

in Eisenstein integers is mathematically natural.  A primitive solution should force an Eisenstein factor to be a unit times a square, then produce a smaller solution unless `m n = 0` or `m^2 = n^2`.

This may be elegant on paper, but in Lean it requires a lot of infrastructure: Eisenstein integers, units, norms, gcd/coprimality of the two factors, parity/unit cases, and a well-founded descent measure.  I would avoid this route unless the repository already has robust Eisenstein integer infrastructure.

## 3. Explicit birational maps

Let

\[
  C : y^2 = x^4 - x^2 + 1,
\]

and choose the affine rational point `(0,1)` as the base point.  For `x ≠ 0`, define

\[
  X = \frac{2(y+1)}{x^2},
  \qquad
  Y = \frac{x(X^2 - 4)}{2}.
\]

Then `(X,Y)` lies on

\[
  E : Y^2 = (X - 1)(X^2 - 4).
\]

A very useful derived relation, avoiding the inverse map in the final classification, is

\[
  x^2 (X^2 - 4) = 4(X - 1).
\]

Conversely, for a point on `E` with `X^2 ≠ 4`, define

\[
  x = \frac{2Y}{X^2 - 4},
  \qquad
  y = \frac{X^2 - 2X + 4}{X^2 - 4}.
\]

Then `(x,y)` lies on `C`.

Exceptional points:

* `(0,1) ∈ C` is the base point and maps to the point at infinity `O` on `E`.
* `(0,-1) ∈ C` corresponds to `(X,Y) = (1,0)`.
* The two projective points at infinity on the quartic correspond to `(X,Y) = (2,0)` and `(X,Y) = (-2,0)`.
* The affine points `(±1,±1)` correspond to `(X,Y) = (0,±2)` and `(4,±6)` with signs as follows:
  * `(1,-1) ↔ (0,-2)`
  * `(-1,-1) ↔ (0,2)`
  * `(1,1) ↔ (4,6)`
  * `(-1,1) ↔ (4,-6)`

Lean-friendly definitions:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- Affine rational quartic `C : y^2 = x^4 - x^2 + 1`. -/
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- Affine Weierstrass model `E : Y^2 = (X - 1)(X^2 - 4)`. -/
def RatEisensteinEC (X Y : ℚ) : Prop :=
  Y ^ 2 = (X - 1) * (X ^ 2 - 4)

/-- Map `C -> E`, valid away from `x = 0`. -/
def quarticToEC_X (x y : ℚ) : ℚ :=
  2 * (y + 1) / x ^ 2

/-- Map `C -> E`, valid away from `x = 0`. -/
def quarticToEC_Y (x y : ℚ) : ℚ :=
  x * (quarticToEC_X x y ^ 2 - 4) / 2

/-- Inverse map `E -> C`, valid away from `X^2 = 4`. -/
def ecToQuartic_x (X Y : ℚ) : ℚ :=
  2 * Y / (X ^ 2 - 4)

/-- Inverse map `E -> C`, valid away from `X^2 = 4`. -/
def ecToQuartic_y (X Y : ℚ) : ℚ :=
  (X ^ 2 - 2 * X + 4) / (X ^ 2 - 4)

/-- The exact affine point list for `E`.  This is the hard arithmetic theorem. -/
def RatEisensteinECAffinePointList (X Y : ℚ) : Prop :=
  (X = -2 ∧ Y = 0) ∨
  (X = 1 ∧ Y = 0) ∨
  (X = 2 ∧ Y = 0) ∨
  (X = 0 ∧ (Y = 2 ∨ Y = -2)) ∨
  (X = 4 ∧ (Y = 6 ∨ Y = -6))

/-- The elliptic-curve finite point theorem to prove in a separate file. -/
def RatEisensteinECAffinePointClassification : Prop :=
  ∀ {X Y : ℚ},
    RatEisensteinEC X Y → RatEisensteinECAffinePointList X Y

/-- The rational quartic theorem actually needed downstream. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ},
    RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1

end MazurProof.RationalPointsN12
```

## 4. Machine-checkable subgoals in dependency order

Here is the finite dependency list I recommend.  The point is to isolate exactly one hard arithmetic theorem; the rest is algebra.

### Algebraic map lemmas, no elliptic-curve group law needed

1. `quarticToEC_mem`

   For `x ≠ 0`, the map sends the quartic to `E`:

   ```lean
   import Mathlib
   import FLT.Assumptions.MazurProof.RationalPointsN12

   namespace MazurProof.RationalPointsN12

   def QuarticToECMemGoal : Prop :=
     ∀ {x y : ℚ},
       x ≠ 0 →
       RatQuarticEisenstein x y →
       RatEisensteinEC (quarticToEC_X x y) (quarticToEC_Y x y)

   end MazurProof.RationalPointsN12
   ```

   Proof method: unfold definitions, `field_simp [hx]`, then `ring_nf` or `ring`.

2. `quarticToEC_relation`

   For `X = quarticToEC_X x y`, prove the relation

   \[
     x^2(X^2 - 4) = 4(X - 1).
   \]

   This relation is more useful than the full inverse for the final classification.

   ```lean
   import Mathlib
   import FLT.Assumptions.MazurProof.RationalPointsN12

   namespace MazurProof.RationalPointsN12

   def QuarticToECRelationGoal : Prop :=
     ∀ {x y : ℚ},
       x ≠ 0 →
       RatQuarticEisenstein x y →
       let X := quarticToEC_X x y
       x ^ 2 * (X ^ 2 - 4) = 4 * (X - 1)

   end MazurProof.RationalPointsN12
   ```

   Proof method: from the quartic equation and `X = 2(y+1)/x^2`; again `field_simp [hx]` and `ring`.

3. `ecToQuartic_mem`

   The inverse map sends nonexceptional `E` points back to the quartic:

   ```lean
   import Mathlib
   import FLT.Assumptions.MazurProof.RationalPointsN12

   namespace MazurProof.RationalPointsN12

   def ECToQuarticMemGoal : Prop :=
     ∀ {X Y : ℚ},
       X ^ 2 - 4 ≠ 0 →
       RatEisensteinEC X Y →
       RatQuarticEisenstein (ecToQuartic_x X Y) (ecToQuartic_y X Y)

   end MazurProof.RationalPointsN12
   ```

   This is not strictly needed for the integer theorem, but it is the right sanity check for the birational equivalence.

4. `ratQuartic_xClassification_of_E_points`

   Use `RatEisensteinECAffinePointClassification`, `quarticToEC_mem`, and `quarticToEC_relation`.

   Logic:

   * If `x = 0`, done.
   * If `x ≠ 0`, map to an affine `E` point `(X,Y)`.
   * Apply the finite `E` point list.
   * Cases `X = -2`, `X = 1`, `X = 2` contradict
     \[
       x^2(X^2 - 4) = 4(X - 1)
     \]
     and `x ≠ 0`.
   * Cases `X = 0` and `X = 4` both give `x^2 = 1` from the same relation.

   ```lean
   import Mathlib
   import FLT.Assumptions.MazurProof.RationalPointsN12

   namespace MazurProof.RationalPointsN12

   def RatQuarticXClassificationFromECGoal : Prop :=
     RatEisensteinECAffinePointClassification →
       RatQuarticEisensteinXClassification

   end MazurProof.RationalPointsN12
   ```

### Hard arithmetic theorem for the elliptic curve

5. `RatEisensteinECAffinePointClassification`

   Prove

   ```lean
   ∀ {X Y : ℚ},
     Y ^ 2 = (X - 1) * (X ^ 2 - 4) →
       (X = -2 ∧ Y = 0) ∨
       (X = 1 ∧ Y = 0) ∨
       (X = 2 ∧ Y = 0) ∨
       (X = 0 ∧ (Y = 2 ∨ Y = -2)) ∨
       (X = 4 ∧ (Y = 6 ∨ Y = -6))
   ```

   Recommended proof in its own file:

   * Translate to `E' : V^2 = U(U+1)(U+4)` using `U = X - 2`.
   * Prove `E'(ℚ)` has rank `0` by a hand-coded 2-descent specialized to this curve.
   * Prove torsion is exactly `ℤ/2ℤ × ℤ/4ℤ`; enumerate the seven affine torsion points plus `O`.
   * Translate the finite list back to the `X` model.

   This is the only genuinely deep part.  All other subgoals are rational algebra.

### Integer denominator-clearing lemmas

6. `int_to_ratQuartic`

   If `n ≠ 0` and

   \[
     c^2 = m^4 - m^2n^2 + n^4,
   \]

   then with

   \[
     x = (m : ℚ)/(n : ℚ), \qquad y = (c : ℚ)/(n : ℚ)^2,
   \]

   one has `RatQuarticEisenstein x y`.

   ```lean
   import Mathlib
   import FLT.Assumptions.MazurProof.RationalPointsN12

   namespace MazurProof.RationalPointsN12

   def IntToRatQuarticGoal : Prop :=
     ∀ {m n c : ℤ},
       n ≠ 0 →
       c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
       RatQuarticEisenstein
         ((m : ℚ) / (n : ℚ))
         ((c : ℚ) / (n : ℚ) ^ 2)

   end MazurProof.RationalPointsN12
   ```

   Proof method: cast the integer equation to `ℚ`; use `norm_num` for `(n : ℚ) ≠ 0`; `field_simp`; `ring`.

7. `rat_x_zero_to_int_m_zero`

   If `n ≠ 0` and `(m : ℚ)/(n : ℚ) = 0`, then `m = 0`.

8. `rat_x_sq_one_to_int_sq_eq`

   If `n ≠ 0` and `((m : ℚ)/(n : ℚ))^2 = 1`, then `m^2 = n^2` in `ℤ`.

   Suggested proof: cast to `ℚ`, `field_simp`, get `(m : ℚ)^2 = (n : ℚ)^2`, then use exactness of integer casts.

9. `EisensteinQuarticSquareClassification_of_ratQuartic`

   ```lean
   import Mathlib
   import FLT.Assumptions.MazurProof.RationalPointsN12

   namespace MazurProof.RationalPointsN12

   def EisensteinQuarticSquareClassificationFromRatGoal : Prop :=
     RatQuarticEisensteinXClassification →
       EisensteinQuarticSquareClassification

   end MazurProof.RationalPointsN12
   ```

   Proof structure:

   * Given `m n c` and `h`.
   * By `by_cases hn : n = 0`; if yes, return `Or.inr (Or.inl hn)`.
   * Otherwise build rational point with `IntToRatQuarticGoal`.
   * Apply `RatQuarticEisensteinXClassification`.
   * `x = 0` branch gives `m = 0`.
   * `x^2 = 1` branch gives `m^2 = n^2`.

10. Final assembly:

   ```lean
   import Mathlib
   import FLT.Assumptions.MazurProof.RationalPointsN12

   namespace MazurProof.RationalPointsN12

   def EisensteinQuarticSquareClassificationFromECGoal : Prop :=
     RatEisensteinECAffinePointClassification →
       EisensteinQuarticSquareClassification

   end MazurProof.RationalPointsN12
   ```

   This is just composition of subgoals 4 and 9.

## 5. Why the elliptic curve point list gives exactly the right theorem

Assume `x ≠ 0` and `(x,y) ∈ C(ℚ)`.  Map to `(X,Y) ∈ E(ℚ)`.  From the finite point list on `E`, there are only five affine `X` values:

\[
  X \in \{-2,1,2,0,4\}.
\]

The relation

\[
  x^2(X^2 - 4) = 4(X - 1)
\]

eliminates the exceptional torsion `X` values:

* `X = -2`: left side is `0`, right side is `-12`, impossible.
* `X = 1`: left side is `-3x^2`, right side is `0`, so `x = 0`, contradicting this branch.
* `X = 2`: left side is `0`, right side is `4`, impossible.

The two remaining values give:

* `X = 0`: `-4x^2 = -4`, hence `x^2 = 1`.
* `X = 4`: `12x^2 = 12`, hence `x^2 = 1`.

Together with the separate `x = 0` branch, this proves the rational `x`-classification.

## 6. Sanity checks and false stronger statements to avoid

1. The theorem must allow diagonal residuals.  For every `t : ℤ`,

   \[
     m = n = t, \qquad c = \pm t^2
   \]

   satisfies

   \[
     c^2 = m^4 - m^2 n^2 + n^4.
   \]

   So the stronger statement “no nonzero integer solutions” is false.

2. The theorem must use `m^2 = n^2`, not `m = n`.  The anti-diagonal branch `m = -n` is also real and gives the same diagonal square equality.

3. The branches `m = 0` and `n = 0` are real.  For example, if `m = 0`, then the equation is `c^2 = n^4`, so `c = ± n^2` over integers.

4. Do not require coprimality in the final theorem.  The homogeneous equation scales: if `(m,n,c)` is a solution, then `(k*m,k*n,k^2*c)` is also a solution.  The rational-point route avoids a primitive-normalization detour.

5. Keep both signs of `c`.  The rational point theorem has `y = ±1` at the allowed `x` values.

6. The finite affine point list on `E` intentionally excludes the point at infinity `O`; the quartic base point `(0,1)` maps to `O`.  This is why the rational quartic proof handles `x = 0` before applying the affine map.

7. The inverse map has denominator `X^2 - 4`.  The points `X = ±2` are not affine quartic points under the inverse map; they correspond to projective infinities of the quartic.  In Lean, keep the side condition `X ^ 2 - 4 ≠ 0` on inverse-map lemmas.

## 7. Suggested file split

I would split the work as follows:

```text
FLT/Assumptions/MazurProof/EisensteinQuarticCurve.lean
  - rational quartic and elliptic curve definitions
  - explicit maps
  - algebraic map lemmas
  - statement/proof of RatEisensteinECAffinePointClassification
  - RatQuarticEisensteinXClassification

FLT/Assumptions/MazurProof/RationalPointsN12.lean
  - imports EisensteinQuarticCurve
  - denominator clearing from integers to rationals
  - EisensteinQuarticSquareClassification
  - existing quarticA_no_solution_of_eisensteinQuarticSquareClassification_checked
```

The existing `RationalPointsN12.lean` should then only need the final theorem:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

-- eventual theorem provided by the new curve file:
-- theorem eisensteinQuarticSquareClassification_checked :
--     EisensteinQuarticSquareClassification := ...

end MazurProof.RationalPointsN12
```

The name I recommend for the final checked theorem is

```lean
theorem eisensteinQuarticSquareClassification_checked :
    EisensteinQuarticSquareClassification := ...
```

and the theorem feeding it should be named something like

```lean
theorem ratQuarticEisenstein_xClassification_checked :
    RatQuarticEisensteinXClassification := ...
```

or, if the EC theorem is exposed directly,

```lean
theorem ratEisensteinEC_affinePointClassification_checked :
    RatEisensteinECAffinePointClassification := ...
```

## 8. Practical recommendation

Formalize the algebraic maps and denominator clearing first, with the elliptic point list temporarily represented as a proposition dependency rather than an axiom.  This gives a checked skeleton:

\[
  \text{finite } E(\mathbb Q) \text{ list}
  \Rightarrow
  C(\mathbb Q) \text{ x-classification}
  \Rightarrow
  \text{homogeneous integer classification}
  \Rightarrow
  \text{current A-quartic no-solution theorem}.
\]

Then spend the serious formalization effort on the single theorem

\[
  E(\mathbb Q)_{\mathrm{aff}}
  = \{(-2,0),(1,0),(2,0),(0,\pm2),(4,\pm6)\}.
\]

This keeps the interface honest, avoids accidentally proving a false “no residuals at all” statement, and localizes the only classical arithmetic input to one finite rational-point computation.
