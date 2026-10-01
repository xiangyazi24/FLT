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

private theorem val3_add (x y : ZMod 9) :
    ((x + y).val : ZMod 3) = (x.val : ZMod 3) + (y.val : ZMod 3) := by
  decide +revert

private theorem val3_mul (x y : ZMod 9) :
    ((x * y).val : ZMod 3) = (x.val : ZMod 3) * (y.val : ZMod 3) := by
  decide +revert

private theorem three_lift3_add (x y : ZMod 3) :
    (3 : ZMod 9) * lift3 (x + y) =
      3 * lift3 x + 3 * lift3 y := by
  decide +revert

private theorem lift3_add_three (x y : ZMod 3) :
    lift3 (x + y) * (3 : ZMod 9) =
      lift3 x * 3 + lift3 y * 3 := by
  decide +revert

private theorem mul_lift3_add_three (c : ZMod 9) (x y : ZMod 3) :
    c * lift3 (x + y) * 3 = c * lift3 x * 3 + c * lift3 y * 3 := by
  decide +revert

private theorem lift3_mul_mul_three (x y : ZMod 3) (c : ZMod 9) :
    lift3 (x * y) * c * 3 = lift3 x * lift3 y * c * 3 := by
  decide +revert

private theorem mul_lift3_mul_three (c : ZMod 9) (x y : ZMod 3) :
    c * lift3 (x * y) * 3 = c * lift3 x * lift3 y * 3 := by
  decide +revert

private theorem val3_lift3 (x : ZMod 3) :
    ((lift3 x).val : ZMod 3) = x := by
  decide +revert

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
  decide

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

theorem red3_one : red3 one = 1 := by decide

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

-- Kernel `decide` over the finite `F3^6` table of unit-representative pairs;
-- exhaustive cube-class check (~25 min kernel reduction), heartbeats unbounded.
set_option maxHeartbeats 0 in
theorem unit_reps_distinct :
    ∀ i j k i' j' k' : F3,
      CubeEq5 (unitRep i j k) (unitRep i' j' k') ↔
        i = i' ∧ j = j' ∧ k = k' := by
  decide +revert

/-- Precomputed right-inverse table (indexed by `c0.val*27 + c1.val*3 + c2.val`).
Non-unit slots hold a dummy value; only unit slots are used. -/
private def inv5Table : List R5 := [
⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨1, 0, 0⟩,
  ⟨1, 3, 2⟩,
  ⟨1, 3, 1⟩,
  ⟨7, 2, 1⟩,
  ⟨4, 5, 0⟩,
  ⟨1, 5, 2⟩,
  ⟨4, 1, 1⟩,
  ⟨7, 4, 0⟩,
  ⟨1, 4, 2⟩,
  ⟨1, 6, 0⟩,
  ⟨1, 0, 2⟩,
  ⟨1, 0, 1⟩,
  ⟨7, 8, 1⟩,
  ⟨4, 2, 0⟩,
  ⟨1, 2, 2⟩,
  ⟨4, 7, 1⟩,
  ⟨7, 1, 0⟩,
  ⟨1, 1, 2⟩,
  ⟨1, 3, 0⟩,
  ⟨1, 6, 2⟩,
  ⟨1, 6, 1⟩,
  ⟨7, 5, 1⟩,
  ⟨4, 8, 0⟩,
  ⟨1, 8, 2⟩,
  ⟨4, 4, 1⟩,
  ⟨7, 7, 0⟩,
  ⟨1, 7, 2⟩,
  ⟨5, 0, 0⟩,
  ⟨5, 6, 2⟩,
  ⟨5, 6, 1⟩,
  ⟨2, 8, 2⟩,
  ⟨5, 5, 1⟩,
  ⟨8, 5, 0⟩,
  ⟨8, 1, 2⟩,
  ⟨5, 7, 1⟩,
  ⟨2, 7, 0⟩,
  ⟨5, 6, 0⟩,
  ⟨5, 3, 2⟩,
  ⟨5, 3, 1⟩,
  ⟨2, 5, 2⟩,
  ⟨5, 2, 1⟩,
  ⟨8, 2, 0⟩,
  ⟨8, 7, 2⟩,
  ⟨5, 4, 1⟩,
  ⟨2, 4, 0⟩,
  ⟨5, 3, 0⟩,
  ⟨5, 0, 2⟩,
  ⟨5, 0, 1⟩,
  ⟨2, 2, 2⟩,
  ⟨5, 8, 1⟩,
  ⟨8, 8, 0⟩,
  ⟨8, 4, 2⟩,
  ⟨5, 1, 1⟩,
  ⟨2, 1, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨7, 0, 0⟩,
  ⟨7, 3, 2⟩,
  ⟨7, 3, 1⟩,
  ⟨4, 8, 1⟩,
  ⟨1, 2, 0⟩,
  ⟨7, 2, 2⟩,
  ⟨1, 4, 1⟩,
  ⟨4, 7, 0⟩,
  ⟨7, 7, 2⟩,
  ⟨7, 6, 0⟩,
  ⟨7, 0, 2⟩,
  ⟨7, 0, 1⟩,
  ⟨4, 5, 1⟩,
  ⟨1, 8, 0⟩,
  ⟨7, 8, 2⟩,
  ⟨1, 1, 1⟩,
  ⟨4, 4, 0⟩,
  ⟨7, 4, 2⟩,
  ⟨7, 3, 0⟩,
  ⟨7, 6, 2⟩,
  ⟨7, 6, 1⟩,
  ⟨4, 2, 1⟩,
  ⟨1, 5, 0⟩,
  ⟨7, 5, 2⟩,
  ⟨1, 7, 1⟩,
  ⟨4, 1, 0⟩,
  ⟨7, 1, 2⟩,
  ⟨2, 0, 0⟩,
  ⟨2, 6, 2⟩,
  ⟨2, 6, 1⟩,
  ⟨8, 2, 2⟩,
  ⟨2, 8, 1⟩,
  ⟨5, 8, 0⟩,
  ⟨5, 7, 2⟩,
  ⟨2, 4, 1⟩,
  ⟨8, 4, 0⟩,
  ⟨2, 6, 0⟩,
  ⟨2, 3, 2⟩,
  ⟨2, 3, 1⟩,
  ⟨8, 8, 2⟩,
  ⟨2, 5, 1⟩,
  ⟨5, 5, 0⟩,
  ⟨5, 4, 2⟩,
  ⟨2, 1, 1⟩,
  ⟨8, 1, 0⟩,
  ⟨2, 3, 0⟩,
  ⟨2, 0, 2⟩,
  ⟨2, 0, 1⟩,
  ⟨8, 5, 2⟩,
  ⟨2, 2, 1⟩,
  ⟨5, 2, 0⟩,
  ⟨5, 1, 2⟩,
  ⟨2, 7, 1⟩,
  ⟨8, 7, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨0, 0, 0⟩,
  ⟨4, 0, 0⟩,
  ⟨4, 3, 2⟩,
  ⟨4, 3, 1⟩,
  ⟨1, 5, 1⟩,
  ⟨7, 8, 0⟩,
  ⟨4, 8, 2⟩,
  ⟨7, 7, 1⟩,
  ⟨1, 1, 0⟩,
  ⟨4, 1, 2⟩,
  ⟨4, 6, 0⟩,
  ⟨4, 0, 2⟩,
  ⟨4, 0, 1⟩,
  ⟨1, 2, 1⟩,
  ⟨7, 5, 0⟩,
  ⟨4, 5, 2⟩,
  ⟨7, 4, 1⟩,
  ⟨1, 7, 0⟩,
  ⟨4, 7, 2⟩,
  ⟨4, 3, 0⟩,
  ⟨4, 6, 2⟩,
  ⟨4, 6, 1⟩,
  ⟨1, 8, 1⟩,
  ⟨7, 2, 0⟩,
  ⟨4, 2, 2⟩,
  ⟨7, 1, 1⟩,
  ⟨1, 4, 0⟩,
  ⟨4, 4, 2⟩,
  ⟨8, 0, 0⟩,
  ⟨8, 6, 2⟩,
  ⟨8, 6, 1⟩,
  ⟨5, 5, 2⟩,
  ⟨8, 2, 1⟩,
  ⟨2, 2, 0⟩,
  ⟨2, 4, 2⟩,
  ⟨8, 1, 1⟩,
  ⟨5, 1, 0⟩,
  ⟨8, 6, 0⟩,
  ⟨8, 3, 2⟩,
  ⟨8, 3, 1⟩,
  ⟨5, 2, 2⟩,
  ⟨8, 8, 1⟩,
  ⟨2, 8, 0⟩,
  ⟨2, 1, 2⟩,
  ⟨8, 7, 1⟩,
  ⟨5, 7, 0⟩,
  ⟨8, 3, 0⟩,
  ⟨8, 0, 2⟩,
  ⟨8, 0, 1⟩,
  ⟨5, 8, 2⟩,
  ⟨8, 5, 1⟩,
  ⟨2, 5, 0⟩,
  ⟨2, 7, 2⟩,
  ⟨8, 4, 1⟩,
  ⟨5, 4, 0⟩]

/-- A right inverse for units of `R5`, read off the precomputed table. -/
def inv5 (x : R5) : R5 :=
  inv5Table.getD (x.c0.val * 27 + x.c1.val * 3 + x.c2.val) 0

/-- Precomputed cube-class witness table: for each unit `u`, a tuple
`(i, j, k, r)` with `u = unitRep i j k * r^3` and `r` a unit. -/
private def ucTable : List (F3 × F3 × F3 × R5) := [
(0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨1, 0, 0⟩),
  (2, 2, 2, ⟨1, 1, 0⟩),
  (1, 1, 0, ⟨2, 2, 0⟩),
  (1, 0, 0, ⟨1, 0, 0⟩),
  (0, 2, 1, ⟨2, 0, 0⟩),
  (2, 1, 1, ⟨1, 0, 0⟩),
  (0, 1, 1, ⟨1, 2, 0⟩),
  (2, 0, 0, ⟨1, 0, 0⟩),
  (1, 2, 1, ⟨2, 1, 0⟩),
  (0, 0, 1, ⟨2, 2, 0⟩),
  (2, 2, 0, ⟨1, 2, 0⟩),
  (1, 1, 1, ⟨1, 2, 0⟩),
  (1, 0, 1, ⟨2, 2, 0⟩),
  (0, 2, 2, ⟨1, 1, 0⟩),
  (2, 1, 2, ⟨2, 2, 0⟩),
  (0, 1, 2, ⟨2, 0, 0⟩),
  (2, 0, 1, ⟨2, 2, 0⟩),
  (1, 2, 2, ⟨1, 0, 0⟩),
  (0, 0, 2, ⟨1, 2, 0⟩),
  (2, 2, 1, ⟨2, 0, 0⟩),
  (1, 1, 2, ⟨2, 0, 0⟩),
  (1, 0, 2, ⟨1, 2, 0⟩),
  (0, 2, 0, ⟨1, 2, 0⟩),
  (2, 1, 0, ⟨2, 1, 0⟩),
  (0, 1, 0, ⟨2, 2, 0⟩),
  (2, 0, 2, ⟨1, 2, 0⟩),
  (1, 2, 0, ⟨1, 1, 0⟩),
  (0, 0, 1, ⟨1, 0, 0⟩),
  (1, 1, 1, ⟨2, 2, 0⟩),
  (2, 2, 0, ⟨2, 2, 0⟩),
  (0, 1, 0, ⟨1, 0, 0⟩),
  (1, 2, 0, ⟨2, 0, 0⟩),
  (2, 0, 2, ⟨2, 2, 0⟩),
  (1, 0, 1, ⟨1, 0, 0⟩),
  (2, 1, 2, ⟨1, 0, 0⟩),
  (0, 2, 2, ⟨2, 0, 0⟩),
  (0, 0, 0, ⟨2, 1, 0⟩),
  (1, 1, 0, ⟨1, 0, 0⟩),
  (2, 2, 2, ⟨2, 0, 0⟩),
  (0, 1, 2, ⟨1, 2, 0⟩),
  (1, 2, 2, ⟨2, 1, 0⟩),
  (2, 0, 1, ⟨1, 0, 0⟩),
  (1, 0, 0, ⟨2, 1, 0⟩),
  (2, 1, 1, ⟨2, 1, 0⟩),
  (0, 2, 1, ⟨1, 2, 0⟩),
  (0, 0, 2, ⟨2, 2, 0⟩),
  (1, 1, 2, ⟨1, 2, 0⟩),
  (2, 2, 1, ⟨1, 2, 0⟩),
  (0, 1, 1, ⟨2, 2, 0⟩),
  (1, 2, 1, ⟨1, 1, 0⟩),
  (2, 0, 0, ⟨2, 1, 0⟩),
  (1, 0, 2, ⟨2, 2, 0⟩),
  (2, 1, 0, ⟨1, 1, 0⟩),
  (0, 2, 0, ⟨2, 2, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 2, ⟨1, 0, 0⟩),
  (2, 2, 1, ⟨2, 2, 0⟩),
  (1, 1, 2, ⟨2, 2, 0⟩),
  (1, 0, 1, ⟨2, 1, 0⟩),
  (0, 2, 2, ⟨1, 2, 0⟩),
  (2, 1, 2, ⟨2, 1, 0⟩),
  (0, 1, 1, ⟨1, 0, 0⟩),
  (2, 0, 0, ⟨1, 1, 0⟩),
  (1, 2, 1, ⟨2, 0, 0⟩),
  (0, 0, 0, ⟨1, 1, 0⟩),
  (2, 2, 2, ⟨1, 2, 0⟩),
  (1, 1, 0, ⟨2, 1, 0⟩),
  (1, 0, 2, ⟨1, 0, 0⟩),
  (0, 2, 0, ⟨1, 0, 0⟩),
  (2, 1, 0, ⟨2, 0, 0⟩),
  (0, 1, 2, ⟨2, 2, 0⟩),
  (2, 0, 1, ⟨2, 1, 0⟩),
  (1, 2, 2, ⟨1, 1, 0⟩),
  (0, 0, 1, ⟨2, 1, 0⟩),
  (2, 2, 0, ⟨1, 0, 0⟩),
  (1, 1, 1, ⟨1, 0, 0⟩),
  (1, 0, 0, ⟨1, 1, 0⟩),
  (0, 2, 1, ⟨2, 2, 0⟩),
  (2, 1, 1, ⟨1, 1, 0⟩),
  (0, 1, 0, ⟨2, 1, 0⟩),
  (2, 0, 2, ⟨1, 0, 0⟩),
  (1, 2, 0, ⟨1, 2, 0⟩),
  (0, 0, 2, ⟨2, 0, 0⟩),
  (1, 1, 2, ⟨1, 1, 0⟩),
  (2, 2, 1, ⟨1, 1, 0⟩),
  (0, 1, 0, ⟨1, 2, 0⟩),
  (1, 2, 0, ⟨2, 1, 0⟩),
  (2, 0, 2, ⟨2, 0, 0⟩),
  (1, 0, 0, ⟨2, 2, 0⟩),
  (2, 1, 1, ⟨2, 2, 0⟩),
  (0, 2, 1, ⟨1, 1, 0⟩),
  (0, 0, 1, ⟨1, 2, 0⟩),
  (1, 1, 1, ⟨2, 0, 0⟩),
  (2, 2, 0, ⟨2, 0, 0⟩),
  (0, 1, 2, ⟨1, 1, 0⟩),
  (1, 2, 2, ⟨2, 2, 0⟩),
  (2, 0, 1, ⟨1, 2, 0⟩),
  (1, 0, 2, ⟨2, 0, 0⟩),
  (2, 1, 0, ⟨1, 0, 0⟩),
  (0, 2, 0, ⟨2, 0, 0⟩),
  (0, 0, 0, ⟨2, 2, 0⟩),
  (1, 1, 0, ⟨1, 2, 0⟩),
  (2, 2, 2, ⟨2, 1, 0⟩),
  (0, 1, 1, ⟨2, 0, 0⟩),
  (1, 2, 1, ⟨1, 0, 0⟩),
  (2, 0, 0, ⟨2, 2, 0⟩),
  (1, 0, 1, ⟨1, 2, 0⟩),
  (2, 1, 2, ⟨1, 2, 0⟩),
  (0, 2, 2, ⟨2, 1, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 0, ⟨0, 0, 0⟩),
  (0, 0, 1, ⟨2, 0, 0⟩),
  (2, 2, 0, ⟨1, 1, 0⟩),
  (1, 1, 1, ⟨1, 1, 0⟩),
  (1, 0, 2, ⟨1, 1, 0⟩),
  (0, 2, 0, ⟨1, 1, 0⟩),
  (2, 1, 0, ⟨2, 2, 0⟩),
  (0, 1, 1, ⟨1, 1, 0⟩),
  (2, 0, 0, ⟨1, 2, 0⟩),
  (1, 2, 1, ⟨2, 2, 0⟩),
  (0, 0, 2, ⟨1, 1, 0⟩),
  (2, 2, 1, ⟨2, 1, 0⟩),
  (1, 1, 2, ⟨2, 1, 0⟩),
  (1, 0, 0, ⟨1, 2, 0⟩),
  (0, 2, 1, ⟨2, 1, 0⟩),
  (2, 1, 1, ⟨1, 2, 0⟩),
  (0, 1, 2, ⟨2, 1, 0⟩),
  (2, 0, 1, ⟨2, 0, 0⟩),
  (1, 2, 2, ⟨1, 2, 0⟩),
  (0, 0, 0, ⟨1, 2, 0⟩),
  (2, 2, 2, ⟨1, 0, 0⟩),
  (1, 1, 0, ⟨2, 0, 0⟩),
  (1, 0, 1, ⟨2, 0, 0⟩),
  (0, 2, 2, ⟨1, 0, 0⟩),
  (2, 1, 2, ⟨2, 0, 0⟩),
  (0, 1, 0, ⟨2, 0, 0⟩),
  (2, 0, 2, ⟨1, 1, 0⟩),
  (1, 2, 0, ⟨1, 0, 0⟩),
  (0, 0, 0, ⟨2, 0, 0⟩),
  (1, 1, 0, ⟨1, 1, 0⟩),
  (2, 2, 2, ⟨2, 2, 0⟩),
  (0, 1, 0, ⟨1, 1, 0⟩),
  (1, 2, 0, ⟨2, 2, 0⟩),
  (2, 0, 2, ⟨2, 1, 0⟩),
  (1, 0, 2, ⟨2, 1, 0⟩),
  (2, 1, 0, ⟨1, 2, 0⟩),
  (0, 2, 0, ⟨2, 1, 0⟩),
  (0, 0, 2, ⟨2, 1, 0⟩),
  (1, 1, 2, ⟨1, 0, 0⟩),
  (2, 2, 1, ⟨1, 0, 0⟩),
  (0, 1, 2, ⟨1, 0, 0⟩),
  (1, 2, 2, ⟨2, 0, 0⟩),
  (2, 0, 1, ⟨1, 1, 0⟩),
  (1, 0, 1, ⟨1, 1, 0⟩),
  (2, 1, 2, ⟨1, 1, 0⟩),
  (0, 2, 2, ⟨2, 2, 0⟩),
  (0, 0, 1, ⟨1, 1, 0⟩),
  (1, 1, 1, ⟨2, 1, 0⟩),
  (2, 2, 0, ⟨2, 1, 0⟩),
  (0, 1, 1, ⟨2, 1, 0⟩),
  (1, 2, 1, ⟨1, 2, 0⟩),
  (2, 0, 0, ⟨2, 0, 0⟩),
  (1, 0, 0, ⟨2, 0, 0⟩),
  (2, 1, 1, ⟨2, 0, 0⟩),
  (0, 2, 1, ⟨1, 0, 0⟩)]

/-- The cube-class data `(i, j, k, r)` of a unit, read off the table. -/
def ucData (u : R5) : F3 × F3 × F3 × R5 :=
  ucTable.getD (u.c0.val * 27 + u.c1.val * 3 + u.c2.val) (0, 0, 0, 0)

-- Kernel `decide` over the 243 elements: the existential witnesses are read
-- off `ucData`, so each case is one equality/unit check rather than a search.
set_option maxHeartbeats 0 in
theorem unit_reps_complete :
    ∀ u : R5, IsUnit5 u →
      ∃ i j k : F3, CubeEq5 u (unitRep i j k) := by
  intro u hu
  refine ⟨(ucData u).1, (ucData u).2.1, (ucData u).2.2.1, (ucData u).2.2.2, ?_, ?_⟩
  · revert u; decide
  · revert u; decide

/-- The finite predicate for membership in the local dual Kummer line
generated by the class of `2`. -/
def PassDual3Finite (i j k l : F3) : Prop :=
  l = 0 ∧ ∃ m : F3, CubeEq5 (unitRep i j k) (pow two5 m.val)

instance (i j k l : F3) : Decidable (PassDual3Finite i j k l) := by
  unfold PassDual3Finite
  infer_instance

-- Kernel `decide` over the finite `F3^4` table (each case searches the
-- 243-element ring for a cube witness); default heartbeats are too small.
set_option maxHeartbeats 0 in
theorem passDual3Finite_iff (i j k l : F3) :
    PassDual3Finite i j k l ↔ i = 0 ∧ j = 0 ∧ l = 0 := by
  decide +revert

-- Kernel `decide` over the finite `F3^4` survivor table.
set_option maxHeartbeats 0 in
theorem local_dual_survivor_count :
    (Finset.univ.filter fun c : Fin 4 → F3 ↦
      PassDual3Finite (c 0) (c 1) (c 2) (c 3)).card = 3 := by
  decide

end MazurProof.N18RouteC.LocalThree
