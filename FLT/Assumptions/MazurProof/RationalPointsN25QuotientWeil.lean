import FLT.Assumptions.MazurProof.RationalPointsN25QuotientF2

/-!
# Finite-field moments for the level-25 genus-four quotient

This file extends the kernel-checked point counts for the canonical quotient
`25.150.4.f.1` from `F_2` and `F_4` to `F_8` and `F_16`.  The four counts

`#C(F_2) = 5`, `#C(F_4) = 5`, `#C(F_8) = 20`, `#C(F_16) = 29`

are the point-count moments needed to determine the degree-eight Weil
numerator of a smooth genus-four curve over `F_2`.

The extension fields are executable polynomial-basis models.  The complete
field laws for the cubic model and the inverse law for the quartic model are
checked by ordinary kernel reduction.  The remaining quartic laws are kept in
separate, resource-bounded modules.  Projective points are enumerated by the
unique representative whose first nonzero coordinate is one.  This avoids
quotient enumeration while retaining the exact projective meaning of the
counts once those field-law certificates are imported.

The final section also checks that every *rational* point of the special fibre
has Jacobian rank two.  It deliberately does not claim geometric smoothness:
excluding singular points over the algebraic closure requires a separate
Jacobian-ideal certificate.
-/

namespace MazurProof.RationalPointsN25QuotientWeil

open RationalPointsN25QuotientF2
open scoped BigOperators

-- Finite universal propositions are the trusted computation mechanism in
-- this file, so restore the decision instances disabled by an imported
-- combinatorics module.
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

/-! ## Executable binary-field tables -/

/-- Operations needed to evaluate homogeneous equations in characteristic
two.  Additive inverses equal the original element, so subtraction is
represented by the same operation as addition. -/
structure BinaryRingOperations (R : Type*) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R

/-- Exhaustive algebraic laws certifying that a finite binary operation table,
together with the displayed inverse function, is a field of characteristic
two.  Concrete models can prove these laws independently of the later point
enumeration; the expensive quartic laws are split across dedicated modules. -/
def IsBinaryFieldTable {R : Type*} [DecidableEq R]
    (O : BinaryRingOperations R) (inv : R → R) : Prop :=
  O.zero ≠ O.one ∧
  (∀ a b c, O.add (O.add a b) c = O.add a (O.add b c)) ∧
  (∀ a b, O.add a b = O.add b a) ∧
  (∀ a, O.add O.zero a = a) ∧
  (∀ a, O.add a a = O.zero) ∧
  (∀ a b c, O.mul (O.mul a b) c = O.mul a (O.mul b c)) ∧
  (∀ a b, O.mul a b = O.mul b a) ∧
  (∀ a, O.mul O.one a = a) ∧
  (∀ a, O.mul O.zero a = O.zero) ∧
  (∀ a b c,
    O.mul a (O.add b c) = O.add (O.mul a b) (O.mul a c)) ∧
  (∀ a, a ≠ O.zero → O.mul a (inv a) = O.one)

private instance decidableIsBinaryFieldTable
    {R : Type*} [Fintype R] [DecidableEq R]
    (O : BinaryRingOperations R) (inv : R → R) :
    Decidable (IsBinaryFieldTable O inv) := by
  unfold IsBinaryFieldTable
  infer_instance

/-- Exponentiation using a finite operation table.  The inverse functions
below use the finite-field identity `a⁻¹ = a^(q-2)` for `a ≠ 0`. -/
def binaryPow {R : Type*} (O : BinaryRingOperations R) (a : R) : ℕ → R
  | 0 => O.one
  | n + 1 => O.mul (binaryPow O a n) a

/-! ## The quadratic extension `F_4` -/

/-- The executable field operations on the quadratic model imported from the
previous point-count file. -/
def f4Operations : BinaryRingOperations F4 where
  zero := f4Zero
  one := f4One
  add := f4Add
  mul := f4Mul

/-- Kernel-checked certificate that the imported quadratic operation table is
the four-element field. -/
theorem f4_isBinaryFieldTable :
    IsBinaryFieldTable f4Operations f4Inv := by
  decide

/-! ## The cubic extension `F_8` -/

/-- Addition of binary coefficients, implemented as exclusive-or. -/
def bitAdd (a b : Bool) : Bool :=
  Bool.xor a b

/-- Multiplication of binary coefficients, implemented as conjunction. -/
def bitMul (a b : Bool) : Bool :=
  a && b

/-- Polynomial-basis coordinates for
`F_8 = F_2[alpha]/(alpha^3 + alpha + 1)`.  The element is
`c0 + c1*alpha + c2*alpha^2`. -/
structure F8 where
  c0 : Bool
  c1 : Bool
  c2 : Bool
deriving DecidableEq, Fintype

/-- Addition in the polynomial basis of `F_8`. -/
def f8Add (a b : F8) : F8 :=
  ⟨bitAdd a.c0 b.c0, bitAdd a.c1 b.c1, bitAdd a.c2 b.c2⟩

/-- Multiplication in `F_8`, obtained by binary convolution followed by
`alpha^3 = alpha + 1`. -/
def f8Mul (a b : F8) : F8 :=
  let c0 := bitMul a.c0 b.c0
  let c1 := bitAdd (bitMul a.c0 b.c1) (bitMul a.c1 b.c0)
  let c2 := bitAdd (bitAdd (bitMul a.c0 b.c2) (bitMul a.c1 b.c1))
    (bitMul a.c2 b.c0)
  let c3 := bitAdd (bitMul a.c1 b.c2) (bitMul a.c2 b.c1)
  let c4 := bitMul a.c2 b.c2
  ⟨bitAdd c0 c3, bitAdd (bitAdd c1 c3) c4, bitAdd c2 c4⟩

/-- The executable zero, one, addition, and multiplication table for `F_8`. -/
def f8Operations : BinaryRingOperations F8 where
  zero := ⟨false, false, false⟩
  one := ⟨true, false, false⟩
  add := f8Add
  mul := f8Mul

/-- Inversion in the eight-element field; a nonzero element has inverse
`a^6` because its multiplicative group has order seven. -/
def f8Inv (a : F8) : F8 :=
  binaryPow f8Operations a 6

/-- Every nonzero element of the cubic polynomial-basis table has the
displayed multiplicative inverse, validating projective normalization. -/
theorem f8_mul_inv_of_ne_zero :
    ∀ a : F8, a ≠ f8Operations.zero →
      f8Operations.mul a (f8Inv a) = f8Operations.one := by
  exact of_decide_eq_true rfl

/-- Exhaustive ordinary-kernel certificate that the cubic polynomial-basis
operations form a field of characteristic two.  This connects the executable
`F_8` point enumeration to its intended finite-field interpretation. -/
theorem f8_isBinaryFieldTable :
    IsBinaryFieldTable f8Operations f8Inv := by
  decide

/-- The computational model contains exactly eight elements. -/
theorem f8_card : Fintype.card F8 = 8 := by
  decide

/-! ## The quartic extension `F_16` -/

/-- Polynomial-basis coordinates for
`F_16 = F_2[beta]/(beta^4 + beta + 1)`. -/
structure F16 where
  c0 : Bool
  c1 : Bool
  c2 : Bool
  c3 : Bool
deriving DecidableEq, Fintype

/-- Addition in the polynomial basis of `F_16`. -/
def f16Add (a b : F16) : F16 :=
  ⟨bitAdd a.c0 b.c0, bitAdd a.c1 b.c1,
    bitAdd a.c2 b.c2, bitAdd a.c3 b.c3⟩

/-- Multiplication in `F_16`, obtained by binary convolution followed by
`beta^4 = beta + 1`. -/
def f16Mul (a b : F16) : F16 :=
  let c0 := bitMul a.c0 b.c0
  let c1 := bitAdd (bitMul a.c0 b.c1) (bitMul a.c1 b.c0)
  let c2 := bitAdd (bitAdd (bitMul a.c0 b.c2) (bitMul a.c1 b.c1))
    (bitMul a.c2 b.c0)
  let c3 := bitAdd
    (bitAdd (bitAdd (bitMul a.c0 b.c3) (bitMul a.c1 b.c2))
      (bitMul a.c2 b.c1)) (bitMul a.c3 b.c0)
  let c4 := bitAdd (bitAdd (bitMul a.c1 b.c3) (bitMul a.c2 b.c2))
    (bitMul a.c3 b.c1)
  let c5 := bitAdd (bitMul a.c2 b.c3) (bitMul a.c3 b.c2)
  let c6 := bitMul a.c3 b.c3
  ⟨bitAdd c0 c4, bitAdd (bitAdd c1 c4) c5,
    bitAdd (bitAdd c2 c5) c6, bitAdd c3 c6⟩

/-- The executable zero, one, addition, and multiplication table for
`F_16`. -/
def f16Operations : BinaryRingOperations F16 where
  zero := ⟨false, false, false, false⟩
  one := ⟨true, false, false, false⟩
  add := f16Add
  mul := f16Mul

/-- Inversion in the sixteen-element field; a nonzero element has inverse
`a^14` because its multiplicative group has order fifteen. -/
def f16Inv (a : F16) : F16 :=
  binaryPow f16Operations a 14

/-- Every nonzero element of the quartic polynomial-basis table has the
displayed multiplicative inverse.  This is the field fact needed to justify
first-nonzero-coordinate projective normalization. -/
theorem f16_mul_inv_of_ne_zero :
    ∀ a : F16, a ≠ f16Operations.zero →
      f16Operations.mul a (f16Inv a) = f16Operations.one := by
  exact of_decide_eq_true rfl

/-- The computational model contains exactly sixteen elements. -/
theorem f16_card : Fintype.card F16 = 16 := by
  decide

/-! ## Normalized projective coordinates and canonical equations -/

/-- Unique first-nonzero-coordinate charts for projective three-space.  The
four constructors represent `[1:y:z:w]`, `[0:1:z:w]`, `[0:0:1:w]`, and
`[0:0:0:1]`, respectively. -/
inductive NormalizedProjective4 (R : Type*) where
  | xChart (y z w : R)
  | yChart (z w : R)
  | zChart (w : R)
  | wChart
deriving DecidableEq, Fintype

/-- Convert a normalized projective chart value to its four homogeneous
coordinates using the zero and one of the chosen binary field table. -/
def NormalizedProjective4.coordinates {R : Type*}
    (O : BinaryRingOperations R) : NormalizedProjective4 R → Coordinates4 R
  | .xChart y z w => ⟨O.one, y, z, w⟩
  | .yChart z w => ⟨O.zero, O.one, z, w⟩
  | .zChart w => ⟨O.zero, O.zero, O.one, w⟩
  | .wChart => ⟨O.zero, O.zero, O.zero, O.one⟩

/-- The canonical quadric in characteristic two, evaluated using an explicit
binary field table.  Minus signs disappear because every element is its own
additive inverse. -/
def canonicalQuadric25Binary {R : Type*} (O : BinaryRingOperations R)
    (P : Coordinates4 R) : R :=
  O.add
    (O.add
      (O.add (O.mul P.x P.z) (O.mul P.x P.w))
      (O.mul P.y P.y))
    (O.add (O.mul P.y P.z) (O.mul P.z P.w))

/-- The canonical cubic in characteristic two, evaluated using an explicit
binary field table. -/
def canonicalCubic25Binary {R : Type*} (O : BinaryRingOperations R)
    (P : Coordinates4 R) : R :=
  O.add
    (O.add
      (O.add
        (O.add
          (O.add
            (O.add (O.mul (O.mul P.x P.x) P.w)
              (O.mul (O.mul P.x P.y) P.z))
            (O.mul (O.mul P.x P.y) P.w))
          (O.mul (O.mul P.x P.z) P.w))
        (O.mul (O.mul P.y P.z) P.w))
      (O.mul (O.mul P.z P.z) P.w))
    (O.mul P.z (O.mul P.w P.w))

/-- A normalized projective vector satisfying both canonical equations over
the chosen binary field table. -/
def IsCanonicalNormalized25 {R : Type*} [DecidableEq R]
    (O : BinaryRingOperations R) (P : NormalizedProjective4 R) : Prop :=
  let C := P.coordinates O
  canonicalQuadric25Binary O C = O.zero ∧
    canonicalCubic25Binary O C = O.zero

private instance decidableIsCanonicalNormalized25
    {R : Type*} [DecidableEq R] (O : BinaryRingOperations R) :
    DecidablePred (IsCanonicalNormalized25 O) := fun P => by
  unfold IsCanonicalNormalized25
  infer_instance

/-- The finite set of first-coordinate-normalized canonical points over
`F_4`.  This gives a cardinal form of the earlier no-new-degree-two result. -/
def canonicalNormalizedPoints25F4 : Finset (NormalizedProjective4 F4) :=
  Finset.univ.filter (IsCanonicalNormalized25 f4Operations)

/-- The canonical model has exactly five projective points over `F_4`. -/
theorem canonicalNormalizedPoints25F4_card :
    canonicalNormalizedPoints25F4.card = 5 := by
  set_option maxRecDepth 100000 in
    decide

/-- Canonical points in the chart `[1:y:z:w]` for one fixed `F_8` value of
`y`. -/
def canonicalXChartFiber25F8 (y : F8) : Finset (F8 × F8) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25 f8Operations (.xChart y zw.1 zw.2)

/-- Expected cardinality of each fixed-`y` fibre in the `F_8` `x=1` chart. -/
def expectedXChartFiberCard25F8 (y : F8) : Nat :=
  match y with
  | ⟨false, false, false⟩ => 4
  | ⟨true, false, false⟩ => 1
  | _ => 2

/-- Eight small kernel certificates for the fixed-`y` fibres over `F_8`. -/
theorem canonicalXChartFiber25F8_card :
    ∀ y : F8,
      (canonicalXChartFiber25F8 y).card = expectedXChartFiberCard25F8 y := by
  set_option maxRecDepth 100000 in
    rintro ⟨c0, c1, c2⟩
    cases c0 <;> cases c1 <;> cases c2 <;>
      exact of_decide_eq_true rfl

/-- Canonical points in the normalized chart `[0:1:z:w]` over `F_8`. -/
def canonicalYChartPoints25F8 : Finset (F8 × F8) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25 f8Operations (.yChart zw.1 zw.2)

/-- The `y=1` chart contributes one point over `F_8`. -/
theorem canonicalYChartPoints25F8_card : canonicalYChartPoints25F8.card = 1 := by
  exact of_decide_eq_true rfl

/-- Canonical points in the normalized chart `[0:0:1:w]` over `F_8`. -/
def canonicalZChartPoints25F8 : Finset F8 :=
  Finset.univ.filter fun w =>
    IsCanonicalNormalized25 f8Operations (.zChart w)

/-- The `z=1` chart contributes one point over `F_8`. -/
theorem canonicalZChartPoints25F8_card : canonicalZChartPoints25F8.card = 1 := by
  exact of_decide_eq_true rfl

/-- Projective point count over `F_8`, assembled from the four disjoint
normalized charts. -/
def canonicalProjectivePointCount25F8 : Nat :=
  (∑ y : F8, (canonicalXChartFiber25F8 y).card) +
    canonicalYChartPoints25F8.card + canonicalZChartPoints25F8.card + 1

/-- The canonical model has exactly twenty projective points over `F_8`. -/
theorem canonicalProjectivePointCount25F8_eq :
    canonicalProjectivePointCount25F8 = 20 := by
  classical
  unfold canonicalProjectivePointCount25F8
  rw [Finset.sum_congr rfl (fun y _ => canonicalXChartFiber25F8_card y),
    canonicalYChartPoints25F8_card, canonicalZChartPoints25F8_card]
  exact of_decide_eq_true rfl

/-- Canonical points in the chart `[1:y:z:w]` for one fixed value of `y`.
Splitting the largest projective chart into sixteen fibres keeps each kernel
certificate small. -/
def canonicalXChartFiber25F16 (y : F16) : Finset (F16 × F16) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25 f16Operations (.xChart y zw.1 zw.2)

/-- Expected cardinality of each fixed-`y` fibre in the `x=1` chart. -/
def expectedXChartFiberCard25F16 (y : F16) : Nat :=
  match y with
  | ⟨_, _, _, true⟩ => 1
  | ⟨_, true, true, false⟩ => 4
  | ⟨_, true, false, false⟩ => 2
  | ⟨_, false, true, false⟩ => 2
  | _ => 1

/-
Each lemma below checks one 256-element `(z,w)` fibre.  Keeping the sixteen
certificates separate prevents Lean from constructing one large reduction
term while preserving ordinary kernel checking for every coordinate value.
-/

/-- Kernel certificate for the `y = 0000` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_0000 :
    (canonicalXChartFiber25F16 ⟨false, false, false, false⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 1000` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_1000 :
    (canonicalXChartFiber25F16 ⟨true, false, false, false⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 0100` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_0100 :
    (canonicalXChartFiber25F16 ⟨false, true, false, false⟩).card = 2 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 1100` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_1100 :
    (canonicalXChartFiber25F16 ⟨true, true, false, false⟩).card = 2 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 0010` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_0010 :
    (canonicalXChartFiber25F16 ⟨false, false, true, false⟩).card = 2 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 1010` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_1010 :
    (canonicalXChartFiber25F16 ⟨true, false, true, false⟩).card = 2 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 0110` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_0110 :
    (canonicalXChartFiber25F16 ⟨false, true, true, false⟩).card = 4 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 1110` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_1110 :
    (canonicalXChartFiber25F16 ⟨true, true, true, false⟩).card = 4 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 0001` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_0001 :
    (canonicalXChartFiber25F16 ⟨false, false, false, true⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 1001` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_1001 :
    (canonicalXChartFiber25F16 ⟨true, false, false, true⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 0101` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_0101 :
    (canonicalXChartFiber25F16 ⟨false, true, false, true⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 1101` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_1101 :
    (canonicalXChartFiber25F16 ⟨true, true, false, true⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 0011` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_0011 :
    (canonicalXChartFiber25F16 ⟨false, false, true, true⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 1011` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_1011 :
    (canonicalXChartFiber25F16 ⟨true, false, true, true⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 0111` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_0111 :
    (canonicalXChartFiber25F16 ⟨false, true, true, true⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Kernel certificate for the `y = 1111` fibre of the `F_16` `x=1` chart. -/
private theorem xFiberF16_1111 :
    (canonicalXChartFiber25F16 ⟨true, true, true, true⟩).card = 1 := by
  set_option maxRecDepth 100000 in exact of_decide_eq_true rfl

/-- Sixteen separately reduced certificates for the fibres of the largest
projective chart.  The fibre sizes sum to twenty-six. -/
theorem canonicalXChartFiber25F16_card :
    ∀ y : F16,
      (canonicalXChartFiber25F16 y).card = expectedXChartFiberCard25F16 y := by
  set_option maxRecDepth 100000 in
    rintro ⟨c0, c1, c2, c3⟩
    cases c0
    · cases c1
      · cases c2
        · cases c3
          · exact xFiberF16_0000
          · exact xFiberF16_0001
        · cases c3
          · exact xFiberF16_0010
          · exact xFiberF16_0011
      · cases c2
        · cases c3
          · exact xFiberF16_0100
          · exact xFiberF16_0101
        · cases c3
          · exact xFiberF16_0110
          · exact xFiberF16_0111
    · cases c1
      · cases c2
        · cases c3
          · exact xFiberF16_1000
          · exact xFiberF16_1001
        · cases c3
          · exact xFiberF16_1010
          · exact xFiberF16_1011
      · cases c2
        · cases c3
          · exact xFiberF16_1100
          · exact xFiberF16_1101
        · cases c3
          · exact xFiberF16_1110
          · exact xFiberF16_1111

/-- Canonical points in the normalized chart `[0:1:z:w]` over `F_16`. -/
def canonicalYChartPoints25F16 : Finset (F16 × F16) :=
  Finset.univ.filter fun zw =>
    IsCanonicalNormalized25 f16Operations (.yChart zw.1 zw.2)

/-- The `y=1` projective chart contributes one canonical point. -/
theorem canonicalYChartPoints25F16_card :
    canonicalYChartPoints25F16.card = 1 := by
  exact of_decide_eq_true rfl

/-- Canonical points in the normalized chart `[0:0:1:w]` over `F_16`. -/
def canonicalZChartPoints25F16 : Finset F16 :=
  Finset.univ.filter fun w =>
    IsCanonicalNormalized25 f16Operations (.zChart w)

/-- The `z=1` projective chart contributes one canonical point. -/
theorem canonicalZChartPoints25F16_card :
    canonicalZChartPoints25F16.card = 1 := by
  exact of_decide_eq_true rfl

/-- The normalized point `[0:0:0:1]` lies on both canonical equations over
`F_16`. -/
theorem canonicalWChartPoint25F16 :
    IsCanonicalNormalized25 f16Operations
      (NormalizedProjective4.wChart : NormalizedProjective4 F16) := by
  exact of_decide_eq_true rfl

/-- Projective point count obtained by adding the four disjoint normalized
charts. -/
def canonicalProjectivePointCount25F16 : Nat :=
  (∑ y : F16, (canonicalXChartFiber25F16 y).card) +
    canonicalYChartPoints25F16.card + canonicalZChartPoints25F16.card + 1

/-- The canonical genus-four model has exactly twenty-nine projective points
over `F_16`.  The proof combines sixteen small ordinary-kernel fibre checks
with the three remaining projective charts. -/
theorem canonicalProjectivePointCount25F16_eq :
    canonicalProjectivePointCount25F16 = 29 := by
  classical
  unfold canonicalProjectivePointCount25F16
  rw [Finset.sum_congr rfl (fun y _ => canonicalXChartFiber25F16_card y),
    canonicalYChartPoints25F16_card, canonicalZChartPoints25F16_card]
  exact of_decide_eq_true rfl

/-! ## Jacobian rank at the rational points of the special fibre -/

/-- The gradient of the canonical quadric after reduction to `F_2`. -/
def canonicalQuadricGradient25F2 (P : Coordinates4 F2) : Coordinates4 F2 :=
  ⟨P.z + P.w, P.z, P.x + P.y + P.w, P.x + P.z⟩

/-- The gradient of the canonical cubic after reduction to `F_2`. -/
def canonicalCubicGradient25F2 (P : Coordinates4 F2) : Coordinates4 F2 :=
  ⟨P.y * P.z + P.y * P.w + P.z * P.w,
    P.x * P.z + P.x * P.w + P.z * P.w,
    P.x * P.y + P.x * P.w + P.y * P.w + P.w ^ 2,
    P.x ^ 2 + P.x * P.y + P.x * P.z + P.y * P.z + P.z ^ 2⟩

/-- The six two-by-two minors of the two gradient rows.  A nonzero entry is
equivalent to Jacobian rank two for this codimension-two complete
intersection at the chosen point. -/
def canonicalJacobianMinors25F2 (P : Coordinates4 F2) : List F2 :=
  let q := canonicalQuadricGradient25F2 P
  let k := canonicalCubicGradient25F2 P
  [q.x * k.y - q.y * k.x,
    q.x * k.z - q.z * k.x,
    q.x * k.w - q.w * k.x,
    q.y * k.z - q.z * k.y,
    q.y * k.w - q.w * k.y,
    q.z * k.w - q.w * k.z]

/-- The pointwise Jacobian-rank condition for the canonical complete
intersection over `F_2`. -/
def HasFullCanonicalJacobianRank25F2 (P : Coordinates4 F2) : Prop :=
  ∃ m ∈ canonicalJacobianMinors25F2 P, m ≠ 0

private instance decidableHasFullCanonicalJacobianRank25F2 :
    DecidablePred HasFullCanonicalJacobianRank25F2 := fun P => by
  unfold HasFullCanonicalJacobianRank25F2
  infer_instance

/-- Every `F_2`-rational point of the canonical special fibre has Jacobian
rank two.  Together with the five-point classification this checks all
rational points, but not possible singular closed points of higher degree. -/
theorem canonical_point25F2_has_full_jacobian_rank :
    ∀ P : Coordinates4 F2,
      IsCanonicalPoint25F2 P → HasFullCanonicalJacobianRank25F2 P := by
  decide

end MazurProof.RationalPointsN25QuotientWeil
