import FLT.Assumptions.MazurProof.RationalPointsN25QuotientWeilThreeDefs

/-!
# Linear elimination for the ternary level-25 point counts

On the normalized chart `[1:y:z:w]`, the canonical quadric is linear in
`w`:

```
Q = y^2 + yz - z + (z - 1)w.
```

Away from `z=1`, this determines `w` uniquely.  Substitution into the
cubic leaves one bivariate residual equation.  The exceptional divisor
`z=1` is counted separately.

The first section proves the elimination identity over every field of
characteristic three.  The second section evaluates the resulting residual
over the three small polynomial-basis tables.  The `F_81` calculation is not
performed by a bivariate search here: the order-five Kummer model reduces it
once more to one-dimensional quotient fibres.
-/

namespace MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientWeilThree

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-! ## The characteristic-three elimination identity -/

section Elimination

variable {K : Type*} [Field K] [CharP K 3]

/-- The canonical quadric on the normalized chart `x=1`, written to expose
its coefficient `z-1` of `w`. -/
def canonicalQuadricX25Three (y z w : K) : K :=
  y ^ 2 + y * z - z + (z - 1) * w

/-- The canonical cubic on the normalized chart `x=1`. -/
def canonicalCubicX25Three (y z w : K) : K :=
  w + y * z - y * w - z * w + y * z * w + z ^ 2 * w - z * w ^ 2

/-- The bivariate residual obtained after eliminating `w` from the
quadric-cubic intersection in characteristic three. -/
def canonicalResidualX25Three (y z : K) : K :=
  y ^ 4 * z + y * z ^ 4 + y ^ 3 * z - z ^ 4 +
    y ^ 3 - y ^ 2 + z ^ 2 + z

/-- The quotient multiplying the quadric in the cleared-denominator
elimination identity. -/
def canonicalEliminationMultiplierX25Three (y z w : K) : K :=
  y ^ 2 * z + 2 * y * z ^ 2 + z ^ 3 - z ^ 2 * w -
    2 * y * z + z * w + y + 2 * z - 1

/-- Clearing the linear denominator `z-1` gives the exact identity

`(z-1)^2 C = A Q - R`

in every field of characteristic three.  This is the structural reason the
three-variable point enumeration reduces to a bivariate residual count. -/
theorem canonical_elimination_identity25Three (y z w : K) :
    (z - 1) ^ 2 * canonicalCubicX25Three y z w =
      canonicalEliminationMultiplierX25Three y z w *
        canonicalQuadricX25Three y z w -
      canonicalResidualX25Three y z := by
  unfold canonicalCubicX25Three canonicalEliminationMultiplierX25Three
    canonicalQuadricX25Three canonicalResidualX25Three
  linear_combination
    (-y ^ 3 * z ^ 2 - y ^ 2 * z ^ 3 + y ^ 3 * z + y ^ 2 * z ^ 2 +
      y * z ^ 3 - z ^ 3 * w - y ^ 2 * z - 2 * y * z ^ 2 +
      z ^ 2 * w + y * z + z ^ 2) * CharP.cast_eq_zero K 3

/-- On `z ≠ 1`, a point satisfying the quadric satisfies the cubic exactly
when its bivariate elimination residual vanishes.

The nonzero factor `(z-1)^2` can be cancelled because the ambient type is a
field.  This theorem formally justifies counting one candidate `w` for each
residual pair `(y,z)`. -/
theorem canonicalCubicX25Three_eq_zero_iff_residual
    {y z w : K} (hz : z ≠ 1)
    (hQ : canonicalQuadricX25Three y z w = 0) :
    canonicalCubicX25Three y z w = 0 ↔
      canonicalResidualX25Three y z = 0 := by
  have hD : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hid := canonical_elimination_identity25Three y z w
  rw [hQ, mul_zero] at hid
  constructor
  · intro hC
    have hneg : -canonicalResidualX25Three y z = 0 := by
      simpa [hC] using hid.symm
    exact neg_eq_zero.mp hneg
  · intro hR
    have hprod : (z - 1) ^ 2 * canonicalCubicX25Three y z w = 0 := by
      simpa [hR] using hid
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hD)

end Elimination

/-! ## Executable residual counts -/

/-- The same characteristic-three residual evaluated in an explicit signed
operation table. -/
def canonicalResidualX25Ternary {R : Type*}
    (O : TernaryRingOperations R) (y z : R) : R :=
  let y2 := O.mul y y
  let y3 := O.mul y2 y
  let y4 := O.mul y3 y
  let z2 := O.mul z z
  let z3 := O.mul z2 z
  let z4 := O.mul z3 z
  O.add
    (O.add (O.add (O.mul y4 z) (O.mul y z4)) (O.mul y3 z))
    (O.add (O.neg z4)
      (O.add y3 (O.add (O.neg y2) (O.add z2 z))))

/-- Pairs `(y,z)` on the regular part `z≠1` whose eliminated residual
vanishes.  Each pair determines a unique `w` by the quadric. -/
def canonicalRegularPairs25Three {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Finset (R × R) :=
  Finset.univ.filter fun yz =>
    yz.2 ≠ O.one ∧ canonicalResidualX25Ternary O yz.1 yz.2 = O.zero

/-- Points on the exceptional x-chart divisor `z=1`, where the quadric no
longer determines `w`.  This is a two-variable low-degree fibre. -/
def canonicalExceptionalPairs25Three
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Finset (R × R) :=
  Finset.univ.filter fun yw =>
    IsCanonicalNormalized25Ternary O
      (.xChart yw.1 O.one yw.2)

/-- Points in the normalized projective chart `[0:1:z:w]`. -/
def canonicalYChartPairs25Three
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Finset (R × R) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25Ternary O (.yChart zw.1 zw.2)

/-- Points in the normalized projective chart `[0:0:1:w]`. -/
def canonicalZChartValues25Three
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Finset R :=
  Finset.univ.filter fun w =>
    IsCanonicalNormalized25Ternary O (.zChart w)

/-- Structurally decomposed projective count: regular x-chart residual pairs,
the exceptional divisor `z=1`, the next two normalized charts, and the final
point `[0:0:0:1]`. -/
def canonicalStructuredPointCount25Three
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : TernaryRingOperations R) : Nat :=
  (canonicalRegularPairs25Three O).card +
    (canonicalExceptionalPairs25Three O).card +
    (canonicalYChartPairs25Three O).card +
    (canonicalZChartValues25Three O).card + 1

/-- Over `F_3`, the regular residual locus has two points and the exceptional
divisor has none. -/
theorem canonicalStructuredParts25F3 :
    (canonicalRegularPairs25Three f3Operations).card = 2 ∧
    (canonicalExceptionalPairs25Three f3Operations).card = 0 ∧
    (canonicalYChartPairs25Three f3Operations).card = 1 ∧
    (canonicalZChartValues25Three f3Operations).card = 1 := by
  decide

/-- The structural decomposition recovers `#C(F_3)=5`. -/
theorem canonicalStructuredPointCount25F3_eq :
    canonicalStructuredPointCount25Three f3Operations = 5 := by
  rcases canonicalStructuredParts25F3 with ⟨hR, hE, hY, hZ⟩
  simp [canonicalStructuredPointCount25Three, hR, hE, hY, hZ]

/-- Over `F_9`, the regular residual locus again has two points and the
exceptional divisor has none. -/
theorem canonicalStructuredParts25F9 :
    (canonicalRegularPairs25Three f9Operations).card = 2 ∧
    (canonicalExceptionalPairs25Three f9Operations).card = 0 ∧
    (canonicalYChartPairs25Three f9Operations).card = 1 ∧
    (canonicalZChartValues25Three f9Operations).card = 1 := by
  set_option maxRecDepth 100000 in
    exact of_decide_eq_true rfl

/-- The structural decomposition recovers `#C(F_9)=5`. -/
theorem canonicalStructuredPointCount25F9_eq :
    canonicalStructuredPointCount25Three f9Operations = 5 := by
  rcases canonicalStructuredParts25F9 with ⟨hR, hE, hY, hZ⟩
  simp [canonicalStructuredPointCount25Three, hR, hE, hY, hZ]

/-- Over `F_27`, linear elimination leaves seventeen regular pairs and no
exceptional point. -/
theorem canonicalStructuredParts25F27 :
    (canonicalRegularPairs25Three f27Operations).card = 17 ∧
    (canonicalExceptionalPairs25Three f27Operations).card = 0 ∧
    (canonicalYChartPairs25Three f27Operations).card = 1 ∧
    (canonicalZChartValues25Three f27Operations).card = 1 := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 1000000 in
      exact of_decide_eq_true rfl

/-- The structural decomposition recovers `#C(F_27)=20`. -/
theorem canonicalStructuredPointCount25F27_eq :
    canonicalStructuredPointCount25Three f27Operations = 20 := by
  rcases canonicalStructuredParts25F27 with ⟨hR, hE, hY, hZ⟩
  simp [canonicalStructuredPointCount25Three, hR, hE, hY, hZ]

end MazurProof.RationalPointsN25QuotientWeilThreeLinear
