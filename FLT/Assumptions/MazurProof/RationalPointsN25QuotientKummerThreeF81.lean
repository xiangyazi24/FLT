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

The generic group-theoretic root-count lemma and the projective chart
equivalence are kept logically separate from this terminal table.  This file
records exactly the small residual data they consume.
-/

namespace MazurProof.RationalPointsN25QuotientKummerThreeF81

open MazurProof.RationalPointsN25QuotientWeilThree
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
