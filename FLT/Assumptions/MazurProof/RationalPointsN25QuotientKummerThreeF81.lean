import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF81Field
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientKummerThree

/-!
# One-dimensional `F_81` certificate for the Kummer quotient

The structural file reduces the dense canonical curve to

```
r^5 (1 + A t) + t^2 (B + e^2 t) = 0.
```

For a fixed quotient parameter `t`, the fifth-power map on `F_81^×` has
kernel of order five and image of order sixteen.  Consequently a nonzero
target has five roots exactly when its sixteenth power is one; zero has one
root.  The executable certificate below therefore inspects 81 quotient
parameters, not `81^2` pairs or `81^3` ambient tuples.

The generic group-theoretic root-count lemma is connected below to the
executable table through a genuine field structure on `F81`.  The remaining
projective bookkeeping is kept separate from this terminal certificate.
-/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientKummerThree
open scoped BigOperators

attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-- A primitive fifth root in the polynomial basis
`F_81 = F_3[q]/(q^4+2q^3+2)`: `e=1+2q+2q²`. -/
def f81FifthRoot25 : F81 :=
  ⟨.one, .two, .two, .zero⟩

/-- The square `e²=2+q+2q²`, stored as a literal so the fibre evaluator
does not repeatedly expand the same power. -/
def f81FifthRootSq25 : F81 :=
  ⟨.two, .one, .two, .zero⟩

/-- The Kummer coefficient `A=2e³+e+1=2+2q³`. -/
def f81KummerA25 : F81 :=
  ⟨.two, .zero, .zero, .two⟩

/-- The Kummer coefficient `B=e³+2e²+2e+1=1+2q+q²+q³`. -/
def f81KummerB25 : F81 :=
  ⟨.one, .two, .one, .one⟩

/-- The explicit root and coefficient literals satisfy the cyclotomic and
coefficient identities used by the symbolic Kummer reduction.  This is a
constant-size check in the chosen polynomial basis. -/
theorem f81_kummer_constants_correct :
    let O := f81Operations
    let e := f81FifthRoot25
    let eSq := ternaryPow O e 2
    let eCube := ternaryPow O e 3
    let eFourth := ternaryPow O e 4
    O.add (O.add (O.add (O.add eFourth eCube) eSq) e) O.one = O.zero ∧
    eSq = f81FifthRootSq25 ∧
    O.add (O.add (O.mul (O.neg O.one) eCube) e) O.one = f81KummerA25 ∧
    O.add (O.add (O.add eCube (O.neg eSq)) (O.neg e)) O.one =
      f81KummerB25 := by
  decide

/-! ## Semantic interpretation of the coefficient table -/

/-- The stored element `f81FifthRoot25` satisfies the fifth cyclotomic
equation in the transported characteristic-three field. -/
theorem f81FifthRoot25_isCyclotomic :
    IsCyclotomicFive25Three f81FifthRoot25 := by
  rcases f81_kummer_constants_correct with ⟨h, -, -, -⟩
  rw [ternaryPow_f81Operations_eq_pow,
    ternaryPow_f81Operations_eq_pow,
    ternaryPow_f81Operations_eq_pow,
    f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_one_eq, f81Operations_zero_eq] at h
  exact h

/-- The stored square literal is the actual square of the cyclotomic root. -/
theorem f81FifthRootSq25_eq :
    f81FifthRoot25 ^ 2 = f81FifthRootSq25 := by
  rcases f81_kummer_constants_correct with ⟨-, h, -, -⟩
  rw [ternaryPow_f81Operations_eq_pow] at h
  exact h

/-- The stored coefficient `A` agrees with the structural Kummer
coefficient.  The conversion from `-1` to `2` uses characteristic three. -/
theorem f81KummerA25_eq :
    segreCoefficientA25Three f81FifthRoot25 = f81KummerA25 := by
  rcases f81_kummer_constants_correct with ⟨-, -, h, -⟩
  rw [ternaryPow_f81Operations_eq_pow,
    f81Operations_neg_eq, f81Operations_mul_eq,
    f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_one_eq] at h
  unfold segreCoefficientA25Three
  linear_combination h + f81FifthRoot25 ^ 3 * CharP.cast_eq_zero F81 3

/-- The stored coefficient `B` agrees with the structural Kummer
coefficient, again interpreting the table's negative signs in
characteristic three. -/
theorem f81KummerB25_eq :
    segreCoefficientB25Three f81FifthRoot25 = f81KummerB25 := by
  rcases f81_kummer_constants_correct with ⟨-, -, -, h⟩
  rw [ternaryPow_f81Operations_eq_pow,
    ternaryPow_f81Operations_eq_pow,
    f81Operations_neg_eq, f81Operations_neg_eq,
    f81Operations_add_eq, f81Operations_add_eq,
    f81Operations_add_eq, f81Operations_one_eq] at h
  unfold segreCoefficientB25Three
  linear_combination h + (f81FifthRoot25 ^ 2 + f81FifthRoot25) *
    CharP.cast_eq_zero F81 3

/-- The denominator `1+At` of the Kummer fibre over `t`. -/
def f81KummerDenominator25 (t : F81) : F81 :=
  f81Operations.add f81Operations.one
    (f81Operations.mul f81KummerA25 t)

/-- The numerator `t²(B+e²t)` of the Kummer fibre over `t`. -/
def f81KummerNumerator25 (t : F81) : F81 :=
  f81Operations.mul (f81Operations.mul t t)
    (f81Operations.add f81KummerB25
      (f81Operations.mul f81FifthRootSq25 t))

/-- The number of roots predicted by the cyclic fifth-power map for the
Kummer fibre over `t`.

If the linear coefficient of `r⁵` vanishes, the equation is either empty or
the whole field.  Otherwise its target is zero (one root), a nonzero fifth
power (five roots), or a non-fifth-power (no roots). -/
def f81KummerFiberSize25 (t : F81) : Nat :=
  let O := f81Operations
  let denominator := f81KummerDenominator25 t
  let numerator := f81KummerNumerator25 t
  if denominator = O.zero then
    if numerator = O.zero then 81 else 0
  else
    let target := O.mul (O.neg numerator) (f81Inv denominator)
    if target = O.zero then 1
    else if ternaryPow O target 16 = O.one then 5 else 0

/-- The executable denominator is the denominator in the structural Kummer
model over the actual field `F81`. -/
theorem f81KummerDenominator25_eq (t : F81) :
    f81KummerDenominator25 t =
      canonicalKummerDenominator25Three f81FifthRoot25 t := by
  unfold f81KummerDenominator25 canonicalKummerDenominator25Three
  rw [f81Operations_add_eq, f81Operations_mul_eq,
    f81Operations_one_eq, f81KummerA25_eq]

/-- The executable numerator is the numerator in the structural Kummer
model over the actual field `F81`. -/
theorem f81KummerNumerator25_eq (t : F81) :
    f81KummerNumerator25 t =
      canonicalKummerNumerator25Three f81FifthRoot25 t := by
  unfold f81KummerNumerator25 canonicalKummerNumerator25Three
  rw [f81Operations_mul_eq, f81Operations_mul_eq,
    f81Operations_add_eq, f81Operations_mul_eq,
    f81KummerB25_eq, f81FifthRootSq25_eq]
  ring

/-- The normalized target computed by the executable table is the field
quotient used in the generic Kummer classifier. -/
theorem f81KummerTarget25_eq (t : F81) :
    f81Operations.mul
        (f81Operations.neg
          (canonicalKummerNumerator25Three f81FifthRoot25 t))
        (f81Inv (canonicalKummerDenominator25Three f81FifthRoot25 t)) =
      canonicalKummerTarget25Three f81FifthRoot25 t := by
  unfold canonicalKummerTarget25Three
  rw [f81Operations_mul_eq, f81Operations_neg_eq, f81Inv_eq_inv,
    div_eq_mul_inv]

/-- The executable fibre classifier is exactly the generic 81-element-field
classifier; the table is no longer a separate, untyped computation. -/
theorem f81KummerFiberSize25_eq (t : F81) :
    f81KummerFiberSize25 t =
      canonicalKummerFiberSizeField81 f81FifthRoot25 t := by
  unfold f81KummerFiberSize25 canonicalKummerFiberSizeField81
  rw [f81KummerDenominator25_eq, f81KummerNumerator25_eq]
  simp only [f81Operations_zero_eq, f81Operations_one_eq,
    f81KummerTarget25_eq, ternaryPow_f81Operations_eq_pow,
    canonicalKummerTarget25Three]

/-- For every quotient parameter, the executable number is the actual
cardinality of the Kummer equation's fifth-power fibre. -/
theorem f81_kummer_actual_fiber_card (t : F81) :
    Nat.card {r : F81 //
      r ^ 5 * canonicalKummerDenominator25Three f81FifthRoot25 t +
        canonicalKummerNumerator25Three f81FifthRoot25 t = 0} =
      f81KummerFiberSize25 t := by
  rw [f81KummerFiberSize25_eq]
  exact canonicalKummerFiber_card_field81 (K := F81)
    (e := f81FifthRoot25) (t := t)
    (by
      rw [Nat.card_eq_fintype_card]
      exact ternary_extension_cardinalities.2.2.2)

/-- Among the 81 quotient fibres, 62 are empty, two have one root, seventeen
have five roots, and none is the whole field.  The categories sum to 87
Kummer pairs. -/
theorem f81_kummer_fiber_distribution :
    (Finset.univ.filter fun t : F81 => f81KummerFiberSize25 t = 0).card = 62 ∧
    (Finset.univ.filter fun t : F81 => f81KummerFiberSize25 t = 1).card = 2 ∧
    (Finset.univ.filter fun t : F81 => f81KummerFiberSize25 t = 5).card = 17 ∧
    (Finset.univ.filter fun t : F81 => f81KummerFiberSize25 t = 81).card = 0 := by
  set_option maxRecDepth 100000 in
    exact of_decide_eq_true rfl

/-- The one-dimensional fibre sum contains 87 Kummer pairs. -/
theorem f81_kummer_fiber_sum :
    ∑ t : F81, f81KummerFiberSize25 t = 87 := by
  set_option maxRecDepth 100000 in
    exact of_decide_eq_true rfl

/-- Summing actual root cardinalities over all quotient parameters gives 87
Kummer pairs.  The finite certificate is therefore attached to the genuine
field equation, not merely to the executable classifier. -/
theorem f81_kummer_actual_fiber_sum :
    ∑ t : F81,
      Nat.card {r : F81 //
        r ^ 5 * canonicalKummerDenominator25Three f81FifthRoot25 t +
          canonicalKummerNumerator25Three f81FifthRoot25 t = 0} = 87 := by
  simp_rw [f81_kummer_actual_fiber_card]
  exact f81_kummer_fiber_sum

/-- The projective Kummer-model count subtracts the one point introduced by
clearing `r⁴` at `r=0`, then adds the three explicitly classified points on
the Segre boundary. -/
def f81StructuralKummerPointCount25 : Nat :=
  (∑ t : F81, f81KummerFiberSize25 t) - 1 + 3

/-- The structural Kummer decomposition gives the target value 89 from an
81-fibre certificate and three boundary points. -/
theorem f81StructuralKummerPointCount25_eq :
    f81StructuralKummerPointCount25 = 89 := by
  rw [f81StructuralKummerPointCount25, f81_kummer_fiber_sum]

end MazurProof.RationalPointsN25QuotientKummerThreeF81
