import FLT.Assumptions.MazurProof.N18RouteC_Split
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# The finite local cube-class calculation at the prime above three

Modulo `pi ^ 5`, every element of the completed integer ring has a unique
representative

`c0 + c1 * pi + c2 * pi ^ 2`,

with `c0,c1 : ZMod 9` and `c2 : ZMod 3`.  The relation
`pi ^ 3 = 3 - 3 * pi ^ 2` gives `pi ^ 4 = 3 * pi` in this quotient.
This file performs the resulting `243`-element cube-class calculation.  The
separate arithmetic-soundness layer identifies this finite ring with the
actual quotient of the local integer ring.
-/

namespace MazurProof.N18RouteC.LocalThree

set_option maxRecDepth 4000

abbrev F3 := Fin 3

/-- Coordinate presentation of `O_L / (pi^5)`. -/
@[ext] structure R5 where
  c0 : ZMod 9
  c1 : ZMod 9
  c2 : ZMod 3
  deriving DecidableEq, Fintype

def zero : R5 := ⟨0, 0, 0⟩
def one : R5 := ⟨1, 0, 0⟩

/-- The canonical representative lift used only in terms already multiplied
by `3`; changing the lift changes the result by `9`. -/
def lift3 (x : ZMod 3) : ZMod 9 := x.val

/-- Multiplication after reducing `pi^3 = 3 - 3*pi^2` and
`pi^4 = 3*pi` modulo `pi^5`. -/
def c2Mul (x y : R5) : ZMod 3 :=
  (x.c0.val : ZMod 3) * y.c2 +
    (x.c1.val : ZMod 3) * (y.c1.val : ZMod 3) +
    x.c2 * (y.c0.val : ZMod 3)

def mul (x y : R5) : R5 :=
  ⟨x.c0 * y.c0 + 3 * (x.c1 * lift3 y.c2 + lift3 x.c2 * y.c1),
   x.c0 * y.c1 + x.c1 * y.c0 + 3 * lift3 (x.c2 * y.c2),
   c2Mul x y⟩

def add (x y : R5) : R5 :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩

def neg (x : R5) : R5 := ⟨-x.c0, -x.c1, -x.c2⟩

instance : Zero R5 := ⟨zero⟩
instance : One R5 := ⟨one⟩
instance : Add R5 := ⟨add⟩
instance : Neg R5 := ⟨neg⟩
instance : Mul R5 := ⟨mul⟩

private theorem add_assoc_r5 : ∀ x y z : R5, x + y + z = x + (y + z) := by
  intro x y z
  change add (add x y) z = add x (add y z)
  ext <;> simp [add, add_assoc]

private theorem zero_add_r5 : ∀ x : R5, 0 + x = x := by
  intro x; change add zero x = x; ext <;> simp [add, zero]

private theorem neg_add_cancel_r5 : ∀ x : R5, -x + x = 0 := by
  intro x; change add (neg x) x = zero; ext <;> simp [add, neg, zero]

private def red9to3 : ZMod 9 →+* ZMod 3 :=
  ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)

private theorem val3_eq_red9to3 (x : ZMod 9) :
    (x.val : ZMod 3) = red9to3 x := by
  simp only [red9to3, ZMod.castHom_apply, ← ZMod.natCast_val]

private theorem val3_add (x y : ZMod 9) :
    ((x + y).val : ZMod 3) = (x.val : ZMod 3) + (y.val : ZMod 3) := by
  simp only [val3_eq_red9to3, map_add]

private theorem val3_mul (x y : ZMod 9) :
    ((x * y).val : ZMod 3) = (x.val : ZMod 3) * (y.val : ZMod 3) := by
  simp only [val3_eq_red9to3, map_mul]

private theorem three_lift3_add (x y : ZMod 3) :
    (3 : ZMod 9) * lift3 (x + y) =
      3 * lift3 x + 3 * lift3 y := by
  revert x y
  decide

private theorem lift3_add_three (x y : ZMod 3) :
    lift3 (x + y) * (3 : ZMod 9) =
      lift3 x * 3 + lift3 y * 3 := by
  revert x y
  decide

private theorem mul_lift3_add_three (c : ZMod 9) (x y : ZMod 3) :
    c * lift3 (x + y) * 3 = c * lift3 x * 3 + c * lift3 y * 3 := by
  revert c x y
  decide

private theorem lift3_mul_mul_three (x y : ZMod 3) (c : ZMod 9) :
    lift3 (x * y) * c * 3 = lift3 x * lift3 y * c * 3 := by
  revert x y c
  decide

private theorem mul_lift3_mul_three (c : ZMod 9) (x y : ZMod 3) :
    c * lift3 (x * y) * 3 = c * lift3 x * lift3 y * 3 := by
  revert c x y
  decide

private theorem val3_lift3 (x : ZMod 3) :
    ((lift3 x).val : ZMod 3) = x := by
  revert x
  decide

private theorem val3_three : (((3 : ZMod 9).val : ZMod 3)) = 0 := by
  decide

/-- Multiplication by `3` in `ZMod 9` only sees the residue modulo `3`.
This lets us prove the `pi^2`-coefficient carry identities structurally,
reducing them to `ZMod 3` polynomial identities instead of enumerating `R5`. -/
private theorem reduce_mul_three :
    ∀ a b : ZMod 9, (a.val : ZMod 3) = (b.val : ZMod 3) → a * 3 = b * 3 := by
  decide

private theorem reduce_three_mul :
    ∀ a b : ZMod 9, (a.val : ZMod 3) = (b.val : ZMod 3) → 3 * a = 3 * b := by
  decide

private theorem lift3_c2Mul_mul_three (x y : R5) (c : ZMod 9) :
    lift3 (c2Mul x y) * c * 3 =
      (x.c0 * lift3 y.c2 + x.c1 * y.c1 + lift3 x.c2 * y.c0) * c * 3 := by
  refine reduce_mul_three _ _ ?_
  simp only [c2Mul, val3_mul, val3_add, val3_lift3]

private theorem mul_lift3_c2Mul_three (c : ZMod 9) (x y : R5) :
    c * lift3 (c2Mul x y) * 3 =
      c * (x.c0 * lift3 y.c2 + x.c1 * y.c1 + lift3 x.c2 * y.c0) * 3 := by
  refine reduce_mul_three _ _ ?_
  simp only [c2Mul, val3_mul, val3_add, val3_lift3]

private theorem three_lift3_c2Mul_mul (x y : R5) (z : ZMod 3) :
    (3 : ZMod 9) * lift3 (c2Mul x y * z) =
      3 * (x.c0 * lift3 y.c2 + x.c1 * y.c1 + lift3 x.c2 * y.c0) *
        lift3 z := by
  rw [mul_assoc]
  refine reduce_three_mul _ _ ?_
  simp only [c2Mul, val3_mul, val3_add, val3_lift3]

private theorem three_lift3_mul_c2Mul (x : ZMod 3) (y z : R5) :
    (3 : ZMod 9) * lift3 (x * c2Mul y z) =
      3 * lift3 x *
        (y.c0 * lift3 z.c2 + y.c1 * z.c1 + lift3 y.c2 * z.c0) := by
  rw [mul_assoc]
  refine reduce_three_mul _ _ ?_
  simp only [c2Mul, val3_mul, val3_add, val3_lift3]

private theorem mul_assoc_r5 : ∀ x y z : R5, x * y * z = x * (y * z) := by
  intro x y z
  change mul (mul x y) z = mul x (mul y z)
  ext
  · simp only [mul]
    ring_nf
    rw [lift3_c2Mul_mul_three, mul_lift3_c2Mul_three]
    ring_nf
    have h9 : (9 : ZMod 9) = 0 := by decide
    rw [h9, mul_zero, mul_zero]
  · simp only [mul]
    rw [three_lift3_c2Mul_mul, three_lift3_mul_c2Mul]
    ring_nf
    rw [lift3_mul_mul_three, mul_lift3_mul_three]
    ring
  · simp only [mul, c2Mul, val3_add, val3_mul, val3_lift3, val3_three]
    ring

private theorem mul_comm_r5 : ∀ x y : R5, x * y = y * x := by
  intro x y; change mul x y = mul y x
  ext
  · simp only [mul]; ring
  · simp only [mul]; rw [mul_comm y.c2 x.c2]; ring
  · simp only [mul, c2Mul]; ring

private theorem one_mul_r5 : ∀ x : R5, 1 * x = x := by
  intro x
  change mul one x = x
  ext <;> simp [mul, one, c2Mul, lift3]

private theorem left_distrib_r5 :
    ∀ x y z : R5, x * (y + z) = x * y + x * z := by
  intro x y z
  change mul x (add y z) = add (mul x y) (mul x z)
  ext
  · simp only [mul, add]
    ring_nf
    rw [mul_lift3_add_three]
    ring
  · simp only [mul, add]
    ring_nf
    rw [lift3_add_three]
    ring
  · simp only [mul, add, c2Mul, val3_add]
    ring

instance : CommRing R5 := CommRing.ofMinimalAxioms
  add_assoc_r5 zero_add_r5 neg_add_cancel_r5 mul_assoc_r5
    mul_comm_r5 one_mul_r5 left_distrib_r5

def pow : R5 → ℕ → R5
  | _, 0 => one
  | x, n + 1 => mul (pow x n) x

theorem pow_eq_ring_pow (x : R5) (n : ℕ) : pow x n = x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow, ih, pow_succ]
      rfl

def pi5 : R5 := ⟨0, 1, 0⟩
def a5 : R5 := ⟨1, 1, 0⟩
def aplus5 : R5 := ⟨2, 1, 0⟩
def two5 : R5 := ⟨2, 0, 0⟩

/-- An element of the quotient is a unit exactly when its constant
coefficient is nonzero modulo `3`. -/
def IsUnit5 (x : R5) : Prop := x.c0.val % 3 ≠ 0

/-- The residue of the constant coefficient modulo `3`.  `IsUnit5 x` says this
is nonzero, and this residue is multiplicative, which lets the unit lemmas be
handled structurally in the field `ZMod 3` rather than by enumerating `R5`. -/
def red3 (x : R5) : ZMod 3 := (x.c0.val : ZMod 3)

theorem isUnit5_iff (x : R5) : IsUnit5 x ↔ red3 x ≠ 0 := by
  simp only [IsUnit5, red3, ne_eq, ZMod.natCast_eq_zero_iff,
    Nat.dvd_iff_mod_eq_zero]

theorem red3_mul (x y : R5) : red3 (x * y) = red3 x * red3 y := by
  change red3 (mul x y) = red3 x * red3 y
  simp only [red3, mul, val3_add, val3_mul, val3_three, zero_mul, add_zero]

theorem red3_one : red3 (1 : R5) = 1 := by rfl

/-- Equality modulo multiplication by the cube of a unit. -/
def CubeEq5 (u v : R5) : Prop :=
  ∃ r : R5, IsUnit5 r ∧ u = mul v (pow r 3)

instance (x : R5) : Decidable (IsUnit5 x) := by
  unfold IsUnit5
  infer_instance

instance (u v : R5) : Decidable (CubeEq5 u v) := by
  unfold CubeEq5
  exact Fintype.decidableExistsFintype

def unitRep (i j k : F3) : R5 :=
  mul (mul (pow a5 i.val) (pow aplus5 j.val)) (pow two5 k.val)

theorem card_r5 : Fintype.card R5 = 243 := by
  decide

/-! ## Structural arithmetic in `R5` -/

/-- The six unit cubes are `± cubeForm t`, for `t : ZMod 3`. -/
def cubeForm (t : ZMod 3) : R5 :=
  ⟨1 + 3 * lift3 t, 3 * lift3 t, 0⟩

theorem nine_eq_zero : (9 : R5) = 0 := by
  ext <;> with_unfolding_all rfl

theorem three_mul_pi5_sq : (3 : R5) * pi5 ^ 2 = 0 := by
  ext <;> with_unfolding_all rfl

theorem pi5_cube : pi5 ^ 3 = (3 : R5) := by
  ext <;> with_unfolding_all rfl

theorem pi5_fifth : pi5 ^ 5 = 0 := by
  calc
    pi5 ^ 5 = pi5 ^ 2 * pi5 ^ 3 := by ring
    _ = pi5 ^ 2 * 3 := by rw [pi5_cube]
    _ = 0 := by
      rw [mul_comm]
      exact three_mul_pi5_sq

private theorem red3_add (x y : R5) : red3 (x + y) = red3 x + red3 y := by
  change ((add x y).c0.val : ZMod 3) = _
  simp only [add, red3, val3_add]

private theorem red3_neg (x : R5) : red3 (-x) = -red3 x := by
  change (((-x.c0 : ZMod 9).val : Nat) : ZMod 3) = _
  simp only [red3, val3_eq_red9to3, map_neg]

private theorem red3_sub (x y : R5) : red3 (x - y) = red3 x - red3 y := by
  rw [sub_eq_add_neg, red3_add, red3_neg, sub_eq_add_neg]

private theorem red3_pi5 : red3 pi5 = 0 := by rfl

private theorem residue_is_sign (a : ZMod 3) (ha : a ≠ 0) :
    a = 1 ∨ a = -1 := by
  revert a
  decide

/-- Division by `pi5` on the maximal ideal, checked coefficientwise. -/
private theorem divisible_by_pi_coeffs (a b : ZMod 9) (c : ZMod 3)
    (ha : (a.val : ZMod 3) = 0) :
    (⟨a, b, c⟩ : R5) =
      pi5 * ⟨b, lift3 c, ((a.val / 3 : Nat) : ZMod 3)⟩ := by
  with_unfolding_all decide +revert

theorem eq_pi5_mul_of_red3_eq_zero {x : R5} (hx : red3 x = 0) :
    ∃ y : R5, x = pi5 * y := by
  rcases x with ⟨a, b, c⟩
  exact ⟨⟨b, lift3 c, ((a.val / 3 : Nat) : ZMod 3)⟩,
    divisible_by_pi_coeffs a b c hx⟩

theorem fifth_pow_eq_zero_of_red3_eq_zero {x : R5} (hx : red3 x = 0) :
    x ^ 5 = 0 := by
  obtain ⟨y, rfl⟩ := eq_pi5_mul_of_red3_eq_zero hx
  rw [mul_pow, pi5_fifth, zero_mul]

private def geometricSum4 (n : R5) : R5 :=
  1 + n + n ^ 2 + n ^ 3 + n ^ 4

/-- Inverse given by the finite geometric series in the nilpotent maximal
ideal.  The sign is the residue of the unit modulo `pi5`. -/
def inv5 (x : R5) : R5 :=
  if red3 x = 1 then
    geometricSum4 (1 - x)
  else
    -geometricSum4 (1 + x)

theorem mul_inv5_of_isUnit5 (x : R5) (hx : IsUnit5 x) : x * inv5 x = 1 := by
  have hx0 : red3 x ≠ 0 := (isUnit5_iff x).mp hx
  rcases residue_is_sign (red3 x) hx0 with hpos | hneg
  · have hnred : red3 (1 - x) = 0 := by
      rw [red3_sub, red3_one, hpos, sub_self]
    have hn5 : (1 - x) ^ 5 = 0 := fifth_pow_eq_zero_of_red3_eq_zero hnred
    rw [inv5, if_pos hpos]
    unfold geometricSum4
    calc
      x * (1 + (1 - x) + (1 - x) ^ 2 + (1 - x) ^ 3 + (1 - x) ^ 4) =
          1 - (1 - x) ^ 5 := by ring
      _ = 1 := by rw [hn5]; ring
  · have hnot : red3 x ≠ 1 := by
      rw [hneg]
      decide
    have hnred : red3 (1 + x) = 0 := by
      rw [red3_add, red3_one, hneg]
      ring
    have hn5 : (1 + x) ^ 5 = 0 := fifth_pow_eq_zero_of_red3_eq_zero hnred
    rw [inv5, if_neg hnot]
    unfold geometricSum4
    calc
      x * -(1 + (1 + x) + (1 + x) ^ 2 + (1 + x) ^ 3 + (1 + x) ^ 4) =
          1 - (1 + x) ^ 5 := by ring
      _ = 1 := by rw [hn5]; ring

/-- Every unit is a sign times a principal unit. -/
theorem unit_decomp {x : R5} (hx : IsUnit5 x) :
    ∃ ε ∈ ({1, -1} : Set R5), ∃ y : R5,
      x = ε * (1 + pi5 * y) := by
  have hx0 : red3 x ≠ 0 := (isUnit5_iff x).mp hx
  rcases residue_is_sign (red3 x) hx0 with hpos | hneg
  · have hdiv : red3 (x - 1) = 0 := by
      rw [red3_sub, hpos, red3_one, sub_self]
    obtain ⟨y, hy⟩ := eq_pi5_mul_of_red3_eq_zero hdiv
    refine ⟨1, by simp, y, ?_⟩
    rw [← hy]
    ring
  · have hdiv : red3 (-x - 1) = 0 := by
      rw [red3_sub, red3_neg, hneg, red3_one]
      ring
    obtain ⟨y, hy⟩ := eq_pi5_mul_of_red3_eq_zero hdiv
    refine ⟨-1, by simp, y, ?_⟩
    rw [← hy]
    ring

private theorem reduced_cube_image_coeffs (a b : ZMod 9) (c : ZMod 3) :
    1 + (3 : R5) * pi5 * (⟨a, b, c⟩ : R5) +
        3 * (⟨a, b, c⟩ : R5) ^ 3 = cubeForm (a.val : ZMod 3) := by
  with_unfolding_all decide +revert

/-- Cubing a principal unit only remembers the residue of its constant
coefficient. -/
theorem cube_image (y : R5) :
    (1 + pi5 * y) ^ 3 = cubeForm (y.c0.val : ZMod 3) := by
  calc
    (1 + pi5 * y) ^ 3 =
        1 + (3 * pi5) * y + (3 * pi5 ^ 2) * y ^ 2 + pi5 ^ 3 * y ^ 3 := by ring
    _ = 1 + (3 : R5) * pi5 * y + 3 * y ^ 3 := by
      rw [three_mul_pi5_sq, pi5_cube]
      ring
    _ = cubeForm (y.c0.val : ZMod 3) := by
      rcases y with ⟨a, b, c⟩
      exact reduced_cube_image_coeffs a b c

/-! ## The three structural cube-class coordinates -/

private abbrev low3 (a : ZMod 9) : ZMod 3 := (a.val : ZMod 3)
private abbrev high3 (a : ZMod 9) : ZMod 3 := ((a.val / 3 : Nat) : ZMod 3)

private abbrev normalized0 (a : ZMod 9) : ZMod 9 :=
  if low3 a = 1 then a else -a

private abbrev normalized1 (a b : ZMod 9) : ZMod 9 :=
  if low3 a = 1 then b else -b

private abbrev normalized2 (a : ZMod 9) (c : ZMod 3) : ZMod 3 :=
  if low3 a = 1 then c else -c

private abbrev cubeClassCoords (a b : ZMod 9) (c : ZMod 3) :
    ZMod 3 × ZMod 3 × ZMod 3 :=
  let a' := normalized0 a
  let b' := normalized1 a b
  let c' := normalized2 a c
  (low3 b', c', high3 b' - high3 a' * (1 + low3 b'))

private abbrev cubeClass (x : R5) : ZMod 3 × ZMod 3 × ZMod 3 :=
  cubeClassCoords x.c0 x.c1 x.c2

private theorem cubeClass_neg_coeffs (a b : ZMod 9) (c : ZMod 3)
    (ha : low3 a ≠ 0) :
    cubeClass (-(⟨a, b, c⟩ : R5)) = cubeClass ⟨a, b, c⟩ := by
  with_unfolding_all decide +revert

private theorem cubeClass_mul_cubeForm_coeffs (a b : ZMod 9) (c t : ZMod 3)
    (ha : low3 a ≠ 0) :
    cubeClass ((⟨a, b, c⟩ : R5) * cubeForm t) = cubeClass ⟨a, b, c⟩ := by
  with_unfolding_all decide +revert

private theorem cubeClass_mul_neg_cubeForm_coeffs (a b : ZMod 9) (c t : ZMod 3)
    (ha : low3 a ≠ 0) :
    cubeClass ((⟨a, b, c⟩ : R5) * -cubeForm t) = cubeClass ⟨a, b, c⟩ := by
  with_unfolding_all decide +revert

private abbrev twistNeg (a d : ZMod 9) : Bool :=
  if low3 a = low3 d then false else true

private abbrev twistT (a d : ZMod 9) : ZMod 3 :=
  high3 (normalized0 a) - high3 (normalized0 d)

private abbrev cubeMul0 (d : ZMod 9) (t : ZMod 3) : ZMod 9 :=
  d * (1 + 3 * lift3 t)

private abbrev cubeMul1 (d e : ZMod 9) (t : ZMod 3) : ZMod 9 :=
  d * (3 * lift3 t) + e * (1 + 3 * lift3 t)

private theorem mul_cubeForm_coords (x : R5) (t : ZMod 3) :
    x * cubeForm t = ⟨cubeMul0 x.c0 t, cubeMul1 x.c0 x.c1 t, x.c2⟩ := by
  rcases x with ⟨a, b, c⟩
  with_unfolding_all decide +revert

private theorem mul_neg_cubeForm_coords (x : R5) (t : ZMod 3) :
    x * -cubeForm t =
      ⟨-cubeMul0 x.c0 t, -cubeMul1 x.c0 x.c1 t, -x.c2⟩ := by
  rw [mul_neg, mul_cubeForm_coords]
  rfl

private theorem same_cubeClass_c0 (a d : ZMod 9)
    (ha : low3 a ≠ 0) (hd : low3 d ≠ 0) :
    a = if twistNeg a d then -cubeMul0 d (twistT a d)
      else cubeMul0 d (twistT a d) := by
  with_unfolding_all decide +revert

private theorem same_cubeClass_c1 (a b d e : ZMod 9)
    (ha : low3 a ≠ 0) (hd : low3 d ≠ 0)
    (hq : low3 (normalized1 a b) = low3 (normalized1 d e))
    (hz : high3 (normalized1 a b) -
        high3 (normalized0 a) * (1 + low3 (normalized1 a b)) =
      high3 (normalized1 d e) -
        high3 (normalized0 d) * (1 + low3 (normalized1 d e))) :
    b = if twistNeg a d then -cubeMul1 d e (twistT a d)
      else cubeMul1 d e (twistT a d) := by
  with_unfolding_all decide +revert

private theorem same_cubeClass_c2 (a d : ZMod 9) (c f : ZMod 3)
    (ha : low3 a ≠ 0) (hd : low3 d ≠ 0)
    (hc : normalized2 a c = normalized2 d f) :
    c = if twistNeg a d then -f else f := by
  with_unfolding_all decide +revert

private theorem same_cubeClass_coeffs
    (a b d e : ZMod 9) (c f : ZMod 3)
    (ha : low3 a ≠ 0) (hd : low3 d ≠ 0)
    (hclass : cubeClass (⟨a, b, c⟩ : R5) = cubeClass ⟨d, e, f⟩) :
    ∃ neg : Bool, ∃ t : ZMod 3,
      (⟨a, b, c⟩ : R5) =
        (⟨d, e, f⟩ : R5) * (if neg then -cubeForm t else cubeForm t) := by
  refine ⟨twistNeg a d, twistT a d, ?_⟩
  have hq := congrArg (fun z => z.1) hclass
  have hc := congrArg (fun z => z.2.1) hclass
  have hz := congrArg (fun z => z.2.2) hclass
  by_cases hn : twistNeg a d = true
  · simp only [hn, if_true]
    rw [mul_neg_cubeForm_coords]
    ext
    · simpa [hn] using same_cubeClass_c0 a d ha hd
    · simpa [hn] using same_cubeClass_c1 a b d e ha hd hq hz
    · simpa [hn] using same_cubeClass_c2 a d c f ha hd hc
  · have hn' : twistNeg a d = false := Bool.eq_false_of_not_eq_true hn
    simp [hn']
    rw [mul_cubeForm_coords]
    ext
    · simpa [hn'] using same_cubeClass_c0 a d ha hd
    · simpa [hn'] using same_cubeClass_c1 a b d e ha hd hq hz
    · simpa [hn'] using same_cubeClass_c2 a d c f ha hd hc

private theorem cubeClass_mul_cubeForm (x : R5) (hx : IsUnit5 x) (t : ZMod 3) :
    cubeClass (x * cubeForm t) = cubeClass x := by
  rcases x with ⟨a, b, c⟩
  apply cubeClass_mul_cubeForm_coeffs
  exact (isUnit5_iff ⟨a, b, c⟩).mp hx

private theorem cubeClass_mul_neg_cubeForm (x : R5) (hx : IsUnit5 x) (t : ZMod 3) :
    cubeClass (x * -cubeForm t) = cubeClass x := by
  rcases x with ⟨a, b, c⟩
  apply cubeClass_mul_neg_cubeForm_coeffs
  exact (isUnit5_iff ⟨a, b, c⟩).mp hx

private def cubeRootForm (t : ZMod 3) : R5 :=
  1 + pi5 * ⟨lift3 t, 0, 0⟩

private theorem cubeRootForm_isUnit (t : ZMod 3) : IsUnit5 (cubeRootForm t) := by
  revert t
  decide

private theorem cubeRootForm_cube (t : ZMod 3) : cubeRootForm t ^ 3 = cubeForm t := by
  simpa only [cubeRootForm, val3_lift3] using cube_image (⟨lift3 t, 0, 0⟩ : R5)

private theorem cubeClass_eq_of_cubeEq {u v : R5}
    (hv : IsUnit5 v) (h : CubeEq5 u v) :
    cubeClass u = cubeClass v := by
  rcases h with ⟨r, hr, huv⟩
  rw [pow_eq_ring_pow] at huv
  obtain ⟨ε, hε, y, hy⟩ := unit_decomp hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hε
  rcases hε with rfl | rfl
  · have hr3 : (1 * (1 + pi5 * y)) ^ 3 = cubeForm (y.c0.val : ZMod 3) := by
      simpa using cube_image y
    rw [hy, hr3] at huv
    rw [huv]
    exact cubeClass_mul_cubeForm v hv _
  · have hr3 : ((-1) * (1 + pi5 * y)) ^ 3 = -cubeForm (y.c0.val : ZMod 3) := by
      calc
        ((-1) * (1 + pi5 * y)) ^ 3 = -(1 + pi5 * y) ^ 3 := by ring
        _ = -cubeForm (y.c0.val : ZMod 3) := by rw [cube_image]
    rw [hy, hr3] at huv
    rw [huv]
    exact cubeClass_mul_neg_cubeForm v hv _

private theorem cubeEq_of_cubeClass_eq {u v : R5}
    (hu : IsUnit5 u) (hv : IsUnit5 v) (hclass : cubeClass u = cubeClass v) :
    CubeEq5 u v := by
  rcases u with ⟨a, b, c⟩
  rcases v with ⟨d, e, f⟩
  have ha : low3 a ≠ 0 := (isUnit5_iff ⟨a, b, c⟩).mp hu
  have hd : low3 d ≠ 0 := (isUnit5_iff ⟨d, e, f⟩).mp hv
  obtain ⟨neg, t, heq⟩ := same_cubeClass_coeffs a b d e c f ha hd hclass
  cases neg with
  | false =>
      refine ⟨cubeRootForm t, cubeRootForm_isUnit t, ?_⟩
      change (⟨a, b, c⟩ : R5) = (⟨d, e, f⟩ : R5) * cubeRootForm t ^ 3
      rw [cubeRootForm_cube]
      simpa using heq
  | true =>
      refine ⟨-cubeRootForm t, ?_, ?_⟩
      · exact (isUnit5_iff _).mpr (by
          rw [red3_neg]
          have ht := (isUnit5_iff _).mp (cubeRootForm_isUnit t)
          exact neg_ne_zero.mpr ht)
      · change (⟨a, b, c⟩ : R5) =
          (⟨d, e, f⟩ : R5) * pow (-cubeRootForm t) 3
        rw [pow_eq_ring_pow]
        have hnegcube : (-cubeRootForm t) ^ 3 = -cubeForm t := by
          rw [neg_pow, cubeRootForm_cube]
          norm_num
        calc
          (⟨a, b, c⟩ : R5) = (⟨d, e, f⟩ : R5) * -cubeForm t := by
            simpa using heq
          _ = (⟨d, e, f⟩ : R5) * (-cubeRootForm t) ^ 3 := by
            rw [hnegcube]

private theorem unitRep_isUnit : ∀ i j k : F3, IsUnit5 (unitRep i j k) := by
  decide

private theorem unitRep_cubeClass_bijective :
    ∀ i j k i' j' k' : F3,
      cubeClass (unitRep i j k) = cubeClass (unitRep i' j' k') ↔
        i = i' ∧ j = j' ∧ k = k' := by
  with_unfolding_all decide +revert

private theorem unitRep_cubeClass_surjective :
    ∀ q c z : ZMod 3, ∃ i j k : F3,
      cubeClass (unitRep i j k) = (q, c, z) := by
  with_unfolding_all decide +revert

private theorem cubeEq5_refl (x : R5) : CubeEq5 x x := by
  refine ⟨1, ?_, ?_⟩
  · change IsUnit5 one
    decide
  · change x = x * (1 : R5) ^ 3
    simp

theorem unit_reps_distinct :
    ∀ i j k i' j' k' : F3,
      CubeEq5 (unitRep i j k) (unitRep i' j' k') ↔
        i = i' ∧ j = j' ∧ k = k' := by
  intro i j k i' j' k'
  constructor
  · intro h
    apply (unitRep_cubeClass_bijective i j k i' j' k').mp
    exact cubeClass_eq_of_cubeEq (unitRep_isUnit i' j' k') h
  · rintro ⟨rfl, rfl, rfl⟩
    exact cubeEq5_refl _

theorem unit_reps_complete :
    ∀ u : R5, IsUnit5 u →
      ∃ i j k : F3, CubeEq5 u (unitRep i j k) := by
  intro u hu
  obtain ⟨i, j, k, hclass⟩ :=
    unitRep_cubeClass_surjective (cubeClass u).1 (cubeClass u).2.1 (cubeClass u).2.2
  refine ⟨i, j, k, cubeEq_of_cubeClass_eq hu (unitRep_isUnit i j k) ?_⟩
  simpa only [Prod.ext_iff] using hclass.symm

/-- The finite predicate for membership in the local dual Kummer line
generated by the class of `2`. -/
def PassDual3Finite (i j k l : F3) : Prop :=
  l = 0 ∧ ∃ m : F3, CubeEq5 (unitRep i j k) (pow two5 m.val)

instance (i j k l : F3) : Decidable (PassDual3Finite i j k l) := by
  unfold PassDual3Finite
  infer_instance

theorem passDual3Finite_iff (i j k l : F3) :
    PassDual3Finite i j k l ↔ i = 0 ∧ j = 0 ∧ l = 0 := by
  constructor
  · rintro ⟨hl, m, hm⟩
    have htwo : unitRep 0 0 m = pow two5 m.val := by
      change (1 : R5) * 1 * pow two5 m.val = pow two5 m.val
      simp
    rw [← htwo] at hm
    have hijk := (unit_reps_distinct i j k 0 0 m).mp hm
    exact ⟨hijk.1, hijk.2.1, hl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨rfl, k, ?_⟩
    have htwo : unitRep 0 0 k = pow two5 k.val := by
      change (1 : R5) * 1 * pow two5 k.val = pow two5 k.val
      simp
    rw [← htwo]
    exact cubeEq5_refl _

theorem local_dual_survivor_count :
    (Finset.univ.filter fun c : Fin 4 → F3 ↦
      PassDual3Finite (c 0) (c 1) (c 2) (c 3)).card = 3 := by
  simp_rw [passDual3Finite_iff]
  decide

end MazurProof.N18RouteC.LocalThree
