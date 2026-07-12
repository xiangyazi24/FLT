import FLT.Assumptions.MazurProof.N18RouteC_FieldArithmetic
import FLT.Assumptions.MazurProof.N18RouteC_LocalThree
import FLT.Assumptions.MazurProof.N18RouteC_ThreeAdic

/-!
# Soundness of the finite `pi^5` cube table

The executable table in `N18RouteC_LocalThree` uses coordinates
`Z/9 x Z/9 x Z/3`.  Here we connect those coordinates to the integral
power basis `1, pi, pi^2` of the actual number field.
-/

namespace MazurProof.N18RouteC.LocalThreeSound

open FieldArithmetic LocalThree

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

def reduceInt (c0 c1 c2 : ℤ) : R5 := ⟨c0, c1, c2⟩

@[simp] theorem reduceInt_zero : reduceInt 0 0 0 = zero := rfl
@[simp] theorem reduceInt_one : reduceInt 1 0 0 = one := rfl
@[simp] theorem reduceInt_pi : reduceInt 0 1 0 = pi5 := rfl
@[simp] theorem reduceInt_a : reduceInt 1 1 0 = a5 := rfl
@[simp] theorem reduceInt_aplus : reduceInt 2 1 0 = aplus5 := rfl
@[simp] theorem reduceInt_two : reduceInt 2 0 0 = two5 := rfl

def prodC0 (x0 x1 x2 y0 y1 y2 : ℤ) : ℤ :=
  x0 * y0 + 3 * (x1 * y2 + x2 * y1) - 9 * x2 * y2

def prodC1 (x0 x1 x2 y0 y1 y2 : ℤ) : ℤ :=
  x0 * y1 + x1 * y0 + 3 * x2 * y2

def prodC2 (x0 x1 x2 y0 y1 y2 : ℤ) : ℤ :=
  x0 * y2 + x1 * y1 + x2 * y0 - 3 * (x1 * y2 + x2 * y1) +
    9 * x2 * y2

theorem ofCoords_mul
    (x0 x1 x2 y0 y1 y2 : ℤ) :
    ofCoords x0 x1 x2 * ofCoords y0 y1 y2 =
      ofCoords (prodC0 x0 x1 x2 y0 y1 y2)
        (prodC1 x0 x1 x2 y0 y1 y2)
        (prodC2 x0 x1 x2 y0 y1 y2) := by
  unfold ofCoords prodC0 prodC1 prodC2
  push_cast
  norm_num
  have hpi4 : pi ^ 4 = -9 + 3 * pi + 9 * pi ^ 2 := by
    linear_combination pi * pi_relation - 3 * pi_relation
  ring_nf
  rw [hpi4, pi_cubed]
  ring

private theorem three_lift3_intCast (z : ℤ) :
    (3 : ZMod 9) * lift3 (z : ZMod 3) = 3 * (z : ZMod 9) := by
  have hz : (3 : ℤ) ∣ z - ((z : ZMod 3).val : ℤ) := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((z : ZMod 3).val : ℤ) z 3).mp (by simp)
  rcases hz with ⟨q, hq⟩
  have hcast :
      ((3 * ((z : ZMod 3).val : ℤ) : ℤ) : ZMod 9) =
        ((3 * z : ℤ) : ZMod 9) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨q, ?_⟩
    omega
  simpa [lift3] using hcast

private theorem reduce9to3_intCast (z : ℤ) :
    (((z : ZMod 9).val : ℤ) : ZMod 3) = (z : ZMod 3) := by
  have h9 : (9 : ℤ) ∣ z - ((z : ZMod 9).val : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((z : ZMod 9).val : ℤ) z 9).mp (by simp)
  have h3 : (3 : ℤ) ∣ z - ((z : ZMod 9).val : ℤ) :=
    dvd_trans (by norm_num) h9
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub
    ((z : ZMod 9).val : ℤ) z 3).mpr h3

private theorem reduce9to3_intCast_nat (z : ℤ) :
    ((z : ZMod 9).val : ZMod 3) = (z : ZMod 3) := by
  simpa only [Int.cast_natCast] using reduce9to3_intCast z

theorem reduceInt_mul
    (x0 x1 x2 y0 y1 y2 : ℤ) :
    reduceInt (prodC0 x0 x1 x2 y0 y1 y2)
        (prodC1 x0 x1 x2 y0 y1 y2)
        (prodC2 x0 x1 x2 y0 y1 y2) =
      mul (reduceInt x0 x1 x2) (reduceInt y0 y1 y2) := by
  ext
  · simp only [reduceInt, prodC0, mul]
    push_cast
    have hx := three_lift3_intCast x2
    have hy := three_lift3_intCast y2
    rw [show (9 : ZMod 9) = 0 by decide]
    simp only [zero_mul, sub_zero]
    linear_combination -(x1 : ZMod 9) * hy - (y1 : ZMod 9) * hx
  · simp only [reduceInt, prodC1, mul]
    push_cast
    have hxy :
        (3 : ZMod 9) * lift3 ((x2 : ZMod 3) * (y2 : ZMod 3)) =
          3 * (x2 : ZMod 9) * (y2 : ZMod 9) := by
      simpa only [Int.cast_mul, mul_assoc] using
        three_lift3_intCast (x2 * y2)
    linear_combination -hxy
  · simp only [reduceInt, prodC2, mul, c2Mul]
    push_cast
    rw [reduce9to3_intCast_nat, reduce9to3_intCast_nat,
      reduce9to3_intCast_nat, reduce9to3_intCast_nat]
    rw [show (3 : ZMod 3) = 0 by decide,
      show (9 : ZMod 3) = 0 by decide]
    ring

@[ext] structure IntCoords where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ

def IntCoords.eval (x : IntCoords) : L := ofCoords x.c0 x.c1 x.c2
def IntCoords.red (x : IntCoords) : R5 := reduceInt x.c0 x.c1 x.c2

def IntCoords.one : IntCoords := ⟨1, 0, 0⟩

def IntCoords.mul (x y : IntCoords) : IntCoords :=
  ⟨prodC0 x.c0 x.c1 x.c2 y.c0 y.c1 y.c2,
   prodC1 x.c0 x.c1 x.c2 y.c0 y.c1 y.c2,
   prodC2 x.c0 x.c1 x.c2 y.c0 y.c1 y.c2⟩

def IntCoords.add (x y : IntCoords) : IntCoords :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩

def IntCoords.neg (x : IntCoords) : IntCoords :=
  ⟨-x.c0, -x.c1, -x.c2⟩

def IntCoords.pow : IntCoords → ℕ → IntCoords
  | _, 0 => IntCoords.one
  | x, n + 1 => IntCoords.mul (IntCoords.pow x n) x

@[simp] theorem IntCoords.eval_one : IntCoords.one.eval = 1 := by
  simp [IntCoords.one, IntCoords.eval, ofCoords]

@[simp] theorem IntCoords.red_one : IntCoords.one.red = LocalThree.one := rfl

theorem IntCoords.eval_mul (x y : IntCoords) :
    (x.mul y).eval = x.eval * y.eval := by
  exact (ofCoords_mul x.c0 x.c1 x.c2 y.c0 y.c1 y.c2).symm

theorem IntCoords.red_mul (x y : IntCoords) :
    (x.mul y).red = LocalThree.mul x.red y.red := by
  exact reduceInt_mul x.c0 x.c1 x.c2 y.c0 y.c1 y.c2

theorem IntCoords.eval_add (x y : IntCoords) :
    (x.add y).eval = x.eval + y.eval := by
  simp [IntCoords.add, IntCoords.eval, ofCoords]
  ring

theorem IntCoords.red_add (x y : IntCoords) :
    (x.add y).red = x.red + y.red := by
  change reduceInt (x.c0 + y.c0) (x.c1 + y.c1) (x.c2 + y.c2) =
    LocalThree.add (reduceInt x.c0 x.c1 x.c2) (reduceInt y.c0 y.c1 y.c2)
  ext <;> simp [reduceInt, LocalThree.add]

theorem IntCoords.eval_neg (x : IntCoords) :
    x.neg.eval = -x.eval := by
  simp [IntCoords.neg, IntCoords.eval, ofCoords]
  ring

theorem IntCoords.red_neg (x : IntCoords) :
    x.neg.red = -x.red := by
  change reduceInt (-x.c0) (-x.c1) (-x.c2) =
    LocalThree.neg (reduceInt x.c0 x.c1 x.c2)
  ext <;> simp [reduceInt, LocalThree.neg]

private theorem local_one_mul (r : R5) : LocalThree.mul LocalThree.one r = r := by
  native_decide +revert

private theorem unitRep_zero :
    unitRep (0 : F3) (0 : F3) (0 : F3) = LocalThree.one := by
  native_decide

theorem IntCoords.eval_pow (x : IntCoords) (n : ℕ) :
    (x.pow n).eval = x.eval ^ n := by
  induction n with
  | zero => simp [IntCoords.pow]
  | succ n ih =>
      rw [IntCoords.pow, IntCoords.eval_mul, ih, pow_succ]

theorem IntCoords.red_pow (x : IntCoords) (n : ℕ) :
    (x.pow n).red = LocalThree.pow x.red n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [IntCoords.pow, IntCoords.red_mul, ih]
      rfl

def aCoords : IntCoords := ⟨1, 1, 0⟩
def aplusCoords : IntCoords := ⟨2, 1, 0⟩
def twoCoords : IntCoords := ⟨2, 0, 0⟩

@[simp] theorem eval_aCoords : aCoords.eval = a := by
  simp [aCoords, IntCoords.eval, ofCoords, a]
  ring

@[simp] theorem eval_aplusCoords : aplusCoords.eval = a + 1 := by
  simp [aplusCoords, IntCoords.eval, ofCoords, a]
  ring

@[simp] theorem eval_twoCoords : twoCoords.eval = 2 := by
  simp [twoCoords, IntCoords.eval, ofCoords]

@[simp] theorem red_aCoords : aCoords.red = a5 := rfl
@[simp] theorem red_aplusCoords : aplusCoords.red = aplus5 := rfl
@[simp] theorem red_twoCoords : twoCoords.red = two5 := rfl

def unitCoords (i j k : F3) : IntCoords :=
  IntCoords.mul
    (IntCoords.mul (IntCoords.pow aCoords i.val)
      (IntCoords.pow aplusCoords j.val))
    (IntCoords.pow twoCoords k.val)

theorem eval_unitCoords (i j k : F3) :
    (unitCoords i j k).eval =
      a ^ i.val * (a + 1) ^ j.val * (2 : L) ^ k.val := by
  simp [unitCoords, IntCoords.eval_mul, IntCoords.eval_pow]

theorem red_unitCoords (i j k : F3) :
    (unitCoords i j k).red = unitRep i j k := by
  simp [unitCoords, IntCoords.red_mul, IntCoords.red_pow, unitRep]

private theorem local_pow_three (r : R5) :
    LocalThree.pow r 3 = LocalThree.mul (LocalThree.mul r r) r := by
  native_decide +revert

private theorem local_isUnit_of_mul_eq_one (r s : R5)
    (h : LocalThree.mul r s = LocalThree.one) : IsUnit5 r := by
  native_decide +revert

theorem IntCoords.eval_injective : Function.Injective IntCoords.eval := by
  intro x y h
  have h0 := congrArg (fun z : L ↦ basis.repr z (0 : Fin 3)) h
  have h1 := congrArg (fun z : L ↦ basis.repr z (1 : Fin 3)) h
  have h2 := congrArg (fun z : L ↦ basis.repr z (2 : Fin 3)) h
  apply IntCoords.ext
  · exact_mod_cast (by simpa [IntCoords.eval] using h0)
  · exact_mod_cast (by simpa [IntCoords.eval] using h1)
  · exact_mod_cast (by simpa [IntCoords.eval] using h2)

/-- Canonical integral power-basis coordinates. -/
def coordsOf (u : OL) : IntCoords :=
  ⟨integralPowerBasis.repr u (0 : Fin 3),
   integralPowerBasis.repr u (1 : Fin 3),
   integralPowerBasis.repr u (2 : Fin 3)⟩

theorem eval_coordsOf (u : OL) : (coordsOf u).eval = (u : L) := by
  have hsum := integralPowerBasis.sum_repr u
  rw [Fin.sum_univ_three] at hsum
  have hsumL := congrArg (fun v : OL ↦ (v : L)) hsum
  simpa [coordsOf, IntCoords.eval, ofCoords, Algebra.smul_def,
    integralPowerBasis_coe_L, basis_apply] using hsumL

theorem coordsOf_piInteger :
    coordsOf piInteger = ⟨0, 1, 0⟩ := by
  apply IntCoords.eval_injective
  rw [eval_coordsOf]
  simp [IntCoords.eval, ofCoords]

theorem coordsOf_aInteger :
    coordsOf aInteger = aCoords := by
  apply IntCoords.eval_injective
  rw [eval_coordsOf, eval_aCoords]
  rfl

theorem coordsOf_aplusInteger :
    coordsOf aplusInteger = aplusCoords := by
  apply IntCoords.eval_injective
  rw [eval_coordsOf, eval_aplusCoords]
  rfl

theorem coordsOf_ring_eq (u : OL) :
    u = algebraMap ℤ OL (coordsOf u).c0 +
      algebraMap ℤ OL (coordsOf u).c1 * piInteger +
      algebraMap ℤ OL (coordsOf u).c2 * piInteger ^ 2 := by
  apply Subtype.ext
  change (u : L) =
    ((coordsOf u).c0 : L) + ((coordsOf u).c1 : L) * pi +
      ((coordsOf u).c2 : L) * pi ^ 2
  simpa [IntCoords.eval, ofCoords] using (eval_coordsOf u).symm

theorem coordsOf_zero : coordsOf (0 : OL) = ⟨0, 0, 0⟩ := by
  apply IntCoords.eval_injective
  rw [eval_coordsOf]
  simp [IntCoords.eval, ofCoords]

theorem coordsOf_one : coordsOf (1 : OL) = IntCoords.one := by
  apply IntCoords.eval_injective
  rw [eval_coordsOf, IntCoords.eval_one]
  rfl

theorem coordsOf_add (x y : OL) :
    coordsOf (x + y) = (coordsOf x).add (coordsOf y) := by
  apply IntCoords.eval_injective
  rw [eval_coordsOf, IntCoords.eval_add, eval_coordsOf, eval_coordsOf]
  rfl

theorem coordsOf_neg (x : OL) :
    coordsOf (-x) = (coordsOf x).neg := by
  apply IntCoords.eval_injective
  rw [eval_coordsOf, IntCoords.eval_neg, eval_coordsOf]
  rfl

theorem coordsOf_mul (x y : OL) :
    coordsOf (x * y) = (coordsOf x).mul (coordsOf y) := by
  apply IntCoords.eval_injective
  rw [eval_coordsOf, IntCoords.eval_mul, eval_coordsOf, eval_coordsOf]
  rfl

def reduceOL (u : OL) : R5 := (coordsOf u).red

@[simp] theorem reduceOL_piInteger : reduceOL piInteger = pi5 := by
  rw [reduceOL, coordsOf_piInteger]
  rfl

@[simp] theorem reduceOL_aInteger : reduceOL aInteger = a5 := by
  rw [reduceOL, coordsOf_aInteger, red_aCoords]

@[simp] theorem reduceOL_aplusInteger : reduceOL aplusInteger = aplus5 := by
  rw [reduceOL, coordsOf_aplusInteger, red_aplusCoords]

@[simp] theorem reduceOL_zero : reduceOL 0 = 0 := by
  rw [reduceOL, coordsOf_zero]
  rfl

@[simp] theorem reduceOL_one : reduceOL 1 = 1 := by
  rw [reduceOL, coordsOf_one, IntCoords.red_one]
  rfl

@[simp] theorem reduceOL_add (x y : OL) :
    reduceOL (x + y) = reduceOL x + reduceOL y := by
  simp only [reduceOL, coordsOf_add, IntCoords.red_add]

@[simp] theorem reduceOL_neg (x : OL) : reduceOL (-x) = -reduceOL x := by
  simp only [reduceOL, coordsOf_neg, IntCoords.red_neg]

@[simp] theorem reduceOL_mul (x y : OL) :
    reduceOL (x * y) = reduceOL x * reduceOL y := by
  rw [reduceOL, coordsOf_mul, IntCoords.red_mul]
  rfl

@[simp] theorem reduceOL_sub (x y : OL) :
    reduceOL (x - y) = reduceOL x - reduceOL y := by
  rw [sub_eq_add_neg, reduceOL_add, reduceOL_neg, sub_eq_add_neg]

@[simp] theorem reduceOL_pow (x : OL) (n : ℕ) :
    reduceOL (x ^ n) = reduceOL x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, reduceOL_mul, ih, pow_succ]

def reduceOLHom : OL →+* R5 where
  toFun := reduceOL
  map_zero' := reduceOL_zero
  map_one' := reduceOL_one
  map_add' := reduceOL_add
  map_mul' := reduceOL_mul

@[simp] theorem reduceOLHom_apply (u : OL) : reduceOLHom u = reduceOL u := rfl

theorem reduceOL_isUnit_of_not_mem {u : OL}
    (hu : u ∉ ThreeAdic.primeAboveThree) : IsUnit5 (reduceOL u) := by
  by_contra hunit
  unfold IsUnit5 at hunit
  simp only [not_ne_iff] at hunit
  let z : ℤ := (coordsOf u).c0
  have hval3Nat : 3 ∣ (z : ZMod 9).val := by
    apply Nat.dvd_of_mod_eq_zero
    simpa [reduceOL, IntCoords.red, reduceInt, IsUnit5, z] using hunit
  have hval3 : (3 : ℤ) ∣ ((z : ZMod 9).val : ℤ) := by
    exact_mod_cast hval3Nat
  have hdiff9 : (9 : ℤ) ∣ z - ((z : ZMod 9).val : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((z : ZMod 9).val : ℤ) z 9).mp (by simp)
  have hdiff3 : (3 : ℤ) ∣ z - ((z : ZMod 9).val : ℤ) :=
    dvd_trans (by norm_num) hdiff9
  have hz3 : (3 : ℤ) ∣ z := by
    obtain ⟨r, hr⟩ := hdiff3
    obtain ⟨s, hs⟩ := hval3
    refine ⟨r + s, ?_⟩
    omega
  apply hu
  rw [ThreeAdic.primeAboveThree_eq_span_pi, coordsOf_ring_eq u]
  apply Ideal.add_mem
  · apply Ideal.add_mem
    · obtain ⟨q, hq⟩ := hz3
      rw [show (coordsOf u).c0 = 3 * q by simpa [z] using hq, map_mul]
      exact Ideal.mul_mem_right _ (Ideal.span ({piInteger} : Set OL))
        ThreeAdic.three_mem_span_pi
    · exact (Ideal.span ({piInteger} : Set OL)).mul_mem_left _
        (Ideal.subset_span (Set.mem_singleton piInteger))
  · apply (Ideal.span ({piInteger} : Set OL)).mul_mem_left
    exact (Ideal.span ({piInteger} : Set OL)).pow_mem_of_mem
      (Ideal.subset_span (Set.mem_singleton piInteger)) 2 (by norm_num)

theorem exists_unit_coords (v : (NumberField.RingOfIntegers L)ˣ) :
    ∃ c : IntCoords,
      c.eval = (((v : NumberField.RingOfIntegers L) : L)) := by
  obtain ⟨c0, c1, c2, hc⟩ :=
    ringOfIntegers_exists_integer_coords
      (v : NumberField.RingOfIntegers L)
  exact ⟨⟨c0, c1, c2⟩, hc.symm⟩

theorem red_unit_isUnit (v : (NumberField.RingOfIntegers L)ˣ)
    (c : IntCoords)
    (hc : c.eval = (((v : NumberField.RingOfIntegers L) : L))) :
    IsUnit5 c.red := by
  obtain ⟨d, hd⟩ := exists_unit_coords v⁻¹
  have heval : (c.mul d).eval = IntCoords.one.eval := by
    rw [IntCoords.eval_mul, hc, hd, IntCoords.eval_one]
    change
      (((v : NumberField.RingOfIntegers L) : L)) *
        (((↑v⁻¹ : NumberField.RingOfIntegers L) : L)) = 1
    simp
  have hcoords : c.mul d = IntCoords.one := IntCoords.eval_injective heval
  apply local_isUnit_of_mul_eq_one c.red d.red
  rw [← IntCoords.red_mul, hcoords, IntCoords.red_one]

theorem a_aplus_independent_mod_cube
    (i j : F3) (v : (NumberField.RingOfIntegers L)ˣ)
    (h : a ^ i.val * (a + 1) ^ j.val =
      (((v : NumberField.RingOfIntegers L) : L)) ^ 3) :
    i = 0 ∧ j = 0 := by
  obtain ⟨c, hc⟩ := exists_unit_coords v
  have heval : (unitCoords i j 0).eval = (c.pow 3).eval := by
    rw [eval_unitCoords, IntCoords.eval_pow, hc]
    simp only [Fin.val_zero, pow_zero, mul_one]
    exact h
  have hcoords : unitCoords i j 0 = c.pow 3 :=
    IntCoords.eval_injective heval
  have hred : unitRep i j 0 = LocalThree.pow c.red 3 := by
    rw [← red_unitCoords, hcoords, IntCoords.red_pow]
  have hcunit : IsUnit5 c.red := red_unit_isUnit v c hc
  have hcube : CubeEq5 (unitRep i j 0) (unitRep 0 0 0) := by
    refine ⟨c.red, hcunit, ?_⟩
    rw [hred]
    rw [unitRep_zero, local_one_mul]
  have hall :=
    (unit_reps_distinct i j 0 (0 : F3) (0 : F3) (0 : F3)).mp hcube
  exact ⟨hall.1, hall.2.1⟩

end

end MazurProof.N18RouteC.LocalThreeSound
