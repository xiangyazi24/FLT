import FLT.Assumptions.MazurProof.N18RouteC_LocalThree

/-!
# Structural certificates for homogeneous `pi^5` solubility

The curve equations are reduced modulo `3` to the truncated polynomial ring
`F_3[pi]/(pi^3)`.  Cubes in that ring are constant, so the two nonconstant
coordinates detect membership in the dual Kummer line.  The only finite
check left is the `27`-case identification of those coordinates on the
canonical `unitRep` representatives.
-/

namespace MazurProof.N18RouteC.LocalThree

set_option maxRecDepth 4000

def OnHomogeneous (U D W : R5) : Prop :=
  W * (W - 3 * U * D + 2 * D ^ 3) = U ^ 3

def InDualLine (W : R5) : Prop :=
  ∃ m : F3, CubeEq5 W (pow two5 m.val)

instance (U D W : R5) : Decidable (OnHomogeneous U D W) := by
  unfold OnHomogeneous
  infer_instance

instance (W : R5) : Decidable (InDualLine W) := by
  unfold InDualLine
  exact Fintype.decidableExistsFintype

/-! ## Reduction modulo `3` -/

/-- The quotient `R5/(3) = F_3[pi]/(pi^3)`. -/
@[ext] structure R3 where
  c0 : ZMod 3
  c1 : ZMod 3
  c2 : ZMod 3

private def R3.zero : R3 := ⟨0, 0, 0⟩
private def R3.one : R3 := ⟨1, 0, 0⟩
private def R3.add (x y : R3) : R3 :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩
private def R3.neg (x : R3) : R3 := ⟨-x.c0, -x.c1, -x.c2⟩
private def R3.mul (x y : R3) : R3 :=
  ⟨x.c0 * y.c0,
   x.c0 * y.c1 + x.c1 * y.c0,
   x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0⟩

private instance : Zero R3 := ⟨R3.zero⟩
private instance : One R3 := ⟨R3.one⟩
private instance : Add R3 := ⟨R3.add⟩
private instance : Neg R3 := ⟨R3.neg⟩
private instance : Mul R3 := ⟨R3.mul⟩

private theorem r3_add_assoc : ∀ x y z : R3, x + y + z = x + (y + z) := by
  intro x y z
  change R3.add (R3.add x y) z = R3.add x (R3.add y z)
  ext <;> simp [R3.add, add_assoc]

private theorem r3_zero_add : ∀ x : R3, 0 + x = x := by
  intro x
  change R3.add R3.zero x = x
  ext <;> simp [R3.add, R3.zero]

private theorem r3_neg_add_cancel : ∀ x : R3, -x + x = 0 := by
  intro x
  change R3.add (R3.neg x) x = R3.zero
  ext <;> simp [R3.add, R3.neg, R3.zero]

private theorem r3_mul_assoc : ∀ x y z : R3, x * y * z = x * (y * z) := by
  intro x y z
  change R3.mul (R3.mul x y) z = R3.mul x (R3.mul y z)
  ext <;> simp [R3.mul] <;> ring

private theorem r3_mul_comm : ∀ x y : R3, x * y = y * x := by
  intro x y
  change R3.mul x y = R3.mul y x
  ext <;> simp [R3.mul] <;> ring

private theorem r3_one_mul : ∀ x : R3, 1 * x = x := by
  intro x
  change R3.mul R3.one x = x
  ext <;> simp [R3.mul, R3.one]

private theorem r3_left_distrib :
    ∀ x y z : R3, x * (y + z) = x * y + x * z := by
  intro x y z
  change R3.mul x (R3.add y z) =
    R3.add (R3.mul x y) (R3.mul x z)
  ext <;> simp [R3.mul, R3.add] <;> ring

private instance : CommRing R3 := CommRing.ofMinimalAxioms
  r3_add_assoc r3_zero_add r3_neg_add_cancel r3_mul_assoc
    r3_mul_comm r3_one_mul r3_left_distrib

private def mod3 : ZMod 9 →+* ZMod 3 :=
  ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)

private theorem mod3_apply (x : ZMod 9) : mod3 x = (x.val : ZMod 3) := by
  simp [mod3, ← ZMod.natCast_val]

/-- Reduction of the three coordinates modulo `3`. -/
private def toR3 : R5 →+* R3 where
  toFun x := ⟨mod3 x.c0, mod3 x.c1, x.c2⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by
    change ⟨mod3 (x + y).c0, mod3 (x + y).c1, (x + y).c2⟩ =
      R3.add ⟨mod3 x.c0, mod3 x.c1, x.c2⟩
        ⟨mod3 y.c0, mod3 y.c1, y.c2⟩
    change (⟨mod3 (LocalThree.add x y).c0,
      mod3 (LocalThree.add x y).c1, (LocalThree.add x y).c2⟩ : R3) = _
    ext <;> simp [R3.add, LocalThree.add, map_add]
  map_mul' x y := by
    change ⟨mod3 (x * y).c0, mod3 (x * y).c1, (x * y).c2⟩ =
      R3.mul ⟨mod3 x.c0, mod3 x.c1, x.c2⟩
        ⟨mod3 y.c0, mod3 y.c1, y.c2⟩
    change (⟨mod3 (LocalThree.mul x y).c0,
      mod3 (LocalThree.mul x y).c1, (LocalThree.mul x y).c2⟩ : R3) = _
    ext <;> simp [R3.mul, LocalThree.mul, c2Mul, map_add, map_mul, mod3_apply]

private theorem zmod3_cube (a : ZMod 3) : a * a * a = a := by
  revert a
  decide

private theorem three_r3 : (3 : R3) = 0 := by
  change R3.add (R3.add R3.one R3.one) R3.one = R3.zero
  ext <;> decide

/-- Frobenius kills the nilpotent coordinates in characteristic `3`. -/
private theorem r3_cube (x : R3) : x ^ 3 = ⟨x.c0, 0, 0⟩ := by
  rw [show x ^ 3 = x * x * x by ring]
  change R3.mul (R3.mul x x) x = _
  ext
  · simp only [R3.mul]
    exact zmod3_cube x.c0
  · simp only [R3.mul]
    rw [show x.c0 * x.c0 * x.c1 +
        (x.c0 * x.c1 + x.c1 * x.c0) * x.c0 =
      3 * x.c0 ^ 2 * x.c1 by ring]
    rw [show (3 : ZMod 3) = 0 by decide]
    simp
  · simp only [R3.mul]
    rw [show x.c0 * x.c0 * x.c2 +
          (x.c0 * x.c1 + x.c1 * x.c0) * x.c1 +
          (x.c0 * x.c2 + x.c1 * x.c1 + x.c2 * x.c0) * x.c0 =
        3 * x.c0 ^ 2 * x.c2 + 3 * x.c0 * x.c1 ^ 2 by ring]
    rw [show (3 : ZMod 3) = 0 by decide]
    simp

private theorem r3_sq_tail_zero {x : R3} (hx0 : x.c0 ≠ 0) {q : ZMod 3}
    (hsq : x * x = ⟨q, 0, 0⟩) : x.c1 = 0 ∧ x.c2 = 0 := by
  change R3.mul x x = ⟨q, 0, 0⟩ at hsq
  have h1 := congrArg R3.c1 hsq
  have h2 := congrArg R3.c2 hsq
  simp [R3.mul] at h1 h2
  rw [show x.c0 * x.c1 + x.c1 * x.c0 = 2 * x.c0 * x.c1 by ring] at h1
  have hx1 : x.c1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · rcases mul_eq_zero.mp h with h2 | h0
      · exact False.elim ((show (2 : ZMod 3) ≠ 0 by decide) h2)
      · exact False.elim (hx0 h0)
    · exact h
  refine ⟨hx1, ?_⟩
  rw [hx1] at h2
  simp at h2
  rw [show x.c0 * x.c2 + x.c2 * x.c0 = 2 * x.c0 * x.c2 by ring] at h2
  rcases mul_eq_zero.mp h2 with h | h
  · rcases mul_eq_zero.mp h with h2 | h0
    · exact False.elim ((show (2 : ZMod 3) ≠ 0 by decide) h2)
    · exact False.elim (hx0 h0)
  · exact h

private theorem r3_hom_zero_tail_zero {x : R3} (hx0 : x.c0 ≠ 0)
    (h : x * (x + 2) = 0) : x.c1 = 0 ∧ x.c2 = 0 := by
  change R3.mul x (R3.add x (R3.add R3.one R3.one)) = R3.zero at h
  have h0 := congrArg R3.c0 h
  have h1 := congrArg R3.c1 h
  have h2 := congrArg R3.c2 h
  simp only [R3.mul, R3.add, R3.one, R3.zero] at h0 h1 h2
  have hshift : x.c0 + (1 + 1) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hx0
  have hx1 : x.c1 = 0 := by
    rw [hshift, mul_zero, add_zero] at h1
    have hx1' := (mul_eq_zero.mp h1).resolve_left hx0
    simpa using hx1'
  refine ⟨hx1, ?_⟩
  rw [hshift, hx1] at h2
  simp at h2
  exact h2.resolve_left hx0

private theorem r3_hom_unit_residues
    (a e : ZMod 3) (ha : a ≠ 0) (he : e ≠ 0)
    (h : a * (a + 2) = e) : a = 2 ∧ e = 2 := by
  revert a e
  decide

private theorem r3_hom_unit_first_tail_zero {x : R3} {e : ZMod 3}
    (hx0 : x.c0 ≠ 0) (he : e ≠ 0)
    (h : x * (x + 2) = ⟨e, 0, 0⟩) :
    x.c0 = 2 ∧ e = 2 ∧ x.c1 = 0 := by
  change R3.mul x (R3.add x (R3.add R3.one R3.one)) =
    ⟨e, 0, 0⟩ at h
  have h0 := congrArg R3.c0 h
  have h2 := congrArg R3.c2 h
  simp only [R3.mul, R3.add, R3.one] at h0 h2
  obtain ⟨hxhead, hehead⟩ := r3_hom_unit_residues x.c0 e hx0 he h0
  rw [hxhead] at h2
  have hx1sq : x.c1 * x.c1 = 0 := by
    simp only [add_zero] at h2
    rw [show (2 : ZMod 3) + (1 + 1) = 1 by decide] at h2
    rw [show 2 * x.c2 + x.c1 * x.c1 + x.c2 * 1 =
      3 * x.c2 + x.c1 * x.c1 by ring] at h2
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul, zero_add] at h2
    exact h2
  have hx1 : x.c1 = 0 := mul_self_eq_zero.mp hx1sq
  exact ⟨hxhead, hehead, hx1⟩

/-! ## Structural characterization of the dual line -/

/-- On the canonical representatives, zero nonconstant reduction coordinates
mean precisely that the first two cube-class coordinates vanish. -/
private theorem unitRep_reduction_tail_zero :
    ∀ i j k : F3,
      (toR3 (unitRep i j k)).c1 = 0 →
      (toR3 (unitRep i j k)).c2 = 0 → i = 0 ∧ j = 0 := by
  with_unfolding_all decide +revert

private theorem inDualLine_of_reduction_tail_zero
    (W : R5) (hW : IsUnit5 W)
    (h1 : (toR3 W).c1 = 0) (h2 : (toR3 W).c2 = 0) :
    InDualLine W := by
  obtain ⟨i, j, k, hcube⟩ := unit_reps_complete W hW
  rcases hcube with ⟨r, hr, hwr⟩
  have hwrRing : W = unitRep i j k * r ^ 3 := by
    rw [← pow_eq_ring_pow]
    exact hwr
  have hmap := congrArg toR3 hwrRing
  simp only [map_mul, map_pow, r3_cube] at hmap
  have hr0 : (toR3 r).c0 ≠ 0 := by
    rw [isUnit5_iff] at hr
    simpa [toR3, red3, mod3_apply] using hr
  have hrep1 : (toR3 (unitRep i j k)).c1 = 0 := by
    have heq := congrArg R3.c1 hmap
    change (toR3 W).c1 =
      (R3.mul (toR3 (unitRep i j k)) ⟨(toR3 r).c0, 0, 0⟩).c1 at heq
    simp only [R3.mul, mul_zero, add_zero, zero_add] at heq
    rw [h1] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_right hr0
  have hrep2 : (toR3 (unitRep i j k)).c2 = 0 := by
    have heq := congrArg R3.c2 hmap
    change (toR3 W).c2 =
      (R3.mul (toR3 (unitRep i j k)) ⟨(toR3 r).c0, 0, 0⟩).c2 at heq
    simp only [R3.mul, mul_zero, add_zero, zero_add] at heq
    rw [h2] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_right hr0
  obtain ⟨rfl, rfl⟩ := unitRep_reduction_tail_zero i j k hrep1 hrep2
  refine ⟨k, r, hr, ?_⟩
  have htwo : unitRep 0 0 k = pow two5 k.val := by
    change (1 : R5) * 1 * pow two5 k.val = pow two5 k.val
    simp
  rw [← htwo]
  exact hwr

/-! ## Unit API -/

theorem one_isUnit5 : IsUnit5 (1 : R5) := by
  rw [isUnit5_iff, red3_one]
  exact one_ne_zero

theorem exists_right_inverse5 :
    ∀ x : R5, IsUnit5 x → ∃ y : R5, x * y = 1 := by
  intro x hx
  exact ⟨inv5 x, mul_inv5_of_isUnit5 x hx⟩

theorem isUnit5_of_mul_eq_one :
    ∀ x y : R5, x * y = 1 → IsUnit5 y := by
  intro x y h
  rw [isUnit5_iff]
  intro hy0
  have h1 : red3 (1 : R5) = 1 := red3_one
  have h2 : red3 (x * y) = red3 x * red3 y := red3_mul x y
  rw [h, h1, hy0, mul_zero] at h2
  exact one_ne_zero h2

theorem isUnit5_mul {x y : R5}
    (hx : IsUnit5 x) (hy : IsUnit5 y) : IsUnit5 (x * y) := by
  rw [isUnit5_iff] at hx hy ⊢
  rw [red3_mul]
  exact mul_ne_zero hx hy

/-! ## The chart `D = 1` -/

private theorem onHomogeneous_one_reduction (U W : R5)
    (h : OnHomogeneous U 1 W) :
    toR3 W * (toR3 W + 2) = (⟨(toR3 U).c0, 0, 0⟩ : R3) := by
  have hmap := congrArg toR3 h
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat] at hmap
  rw [r3_cube (toR3 U)] at hmap
  have hone : toR3 (1 : R5) = 1 := map_one toR3
  rw [hone] at hmap
  simpa [three_r3] using hmap

private theorem r5_add_c0 (x y : R5) : (x + y).c0 = x.c0 + y.c0 := by
  change (LocalThree.add x y).c0 = _
  rfl

private theorem r5_add_c1 (x y : R5) : (x + y).c1 = x.c1 + y.c1 := by
  change (LocalThree.add x y).c1 = _
  rfl

private theorem r5_add_c2 (x y : R5) : (x + y).c2 = x.c2 + y.c2 := by
  change (LocalThree.add x y).c2 = _
  rfl

private theorem r5_neg_c0 (x : R5) : (-x).c0 = -x.c0 := by
  change (LocalThree.neg x).c0 = _
  rfl

private theorem r5_neg_c1 (x : R5) : (-x).c1 = -x.c1 := by
  change (LocalThree.neg x).c1 = _
  rfl

private theorem r5_neg_c2 (x : R5) : (-x).c2 = -x.c2 := by
  change (LocalThree.neg x).c2 = _
  rfl

private theorem r5_mul_c0 (x y : R5) :
    (x * y).c0 = x.c0 * y.c0 +
      3 * (x.c1 * lift3 y.c2 + lift3 x.c2 * y.c1) := by
  change (LocalThree.mul x y).c0 = _
  rfl

private theorem r5_mul_c1 (x y : R5) :
    (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 +
      3 * lift3 (x.c2 * y.c2) := by
  change (LocalThree.mul x y).c1 = _
  rfl

private theorem r5_one_c0 : (1 : R5).c0 = 1 := by rfl
private theorem r5_one_c1 : (1 : R5).c1 = 0 := by rfl

private theorem r5_two_c0 : (2 : R5).c0 = 2 := by
  change (LocalThree.add LocalThree.one LocalThree.one).c0 = 2
  rfl

private theorem r5_two_c1 : (2 : R5).c1 = 0 := by
  change (LocalThree.add LocalThree.one LocalThree.one).c1 = 0
  rfl

private theorem r5_two_c2 : (2 : R5).c2 = 0 := by
  change (LocalThree.add LocalThree.one LocalThree.one).c2 = 0
  rfl

private theorem r5_three_mul_c0 (x : R5) : ((3 : R5) * x).c0 = 3 * x.c0 := by
  rw [show (3 : R5) * x = x + x + x by ring]
  simp only [r5_add_c0]
  ring

private theorem r5_three_mul_c1 (x : R5) : ((3 : R5) * x).c1 = 3 * x.c1 := by
  rw [show (3 : R5) * x = x + x + x by ring]
  simp only [r5_add_c1]
  ring

private theorem r5_three_mul_c2 (x : R5) : ((3 : R5) * x).c2 = 0 := by
  rw [show (3 : R5) * x = x + x + x by ring]
  simp only [r5_add_c2]
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [show x.c2 + x.c2 + x.c2 = 3 * x.c2 by ring, h3, zero_mul]

private theorem three_mul_neg_principal_c0 (y : R5) :
    ((3 : R5) * -(1 + pi5 * y)).c0 = -3 := by
  rw [r5_three_mul_c0, r5_neg_c0, r5_add_c0, r5_one_c0, r5_mul_c0]
  simp only [pi5]
  have h9 : (9 : ZMod 9) = 0 := by decide
  ring_nf
  simp [lift3]
  rw [h9, mul_zero]

private theorem three_mul_neg_principal_c1 (y : R5) :
    ((3 : R5) * -(1 + pi5 * y)).c1 = -3 * y.c0 := by
  rw [r5_three_mul_c1, r5_neg_c1, r5_add_c1, r5_one_c1, r5_mul_c1]
  simp [pi5, lift3]

private theorem three_mul_neg_principal_c2 (y : R5) :
    ((3 : R5) * -(1 + pi5 * y)).c2 = 0 := r5_three_mul_c2 _

private def high9 (a : ZMod 9) : ZMod 3 := ((a.val / 3 : Nat) : ZMod 3)

private theorem zmod9_decomp (a : ZMod 9) :
    a = lift3 (mod3 a) + 3 * lift3 (high9 a) := by
  revert a
  decide

private theorem lift3_zero : lift3 (0 : ZMod 3) = (0 : ZMod 9) := by rfl
private theorem lift3_two : lift3 (2 : ZMod 3) = (2 : ZMod 9) := by rfl

private theorem three_mul_eq_three_lift_mod3 (a : ZMod 9) :
    3 * a = 3 * lift3 (mod3 a) := by
  have h9 : (9 : ZMod 9) = 0 := by decide
  calc
    3 * a = 3 * (lift3 (mod3 a) + 3 * lift3 (high9 a)) := by
      exact congrArg (fun z : ZMod 9 => 3 * z) (zmod9_decomp a)
    _ = 3 * lift3 (mod3 a) := by
      calc
        3 * (lift3 (mod3 a) + 3 * lift3 (high9 a)) =
            3 * lift3 (mod3 a) + 9 * lift3 (high9 a) := by ring
        _ = 3 * lift3 (mod3 a) := by rw [h9, zero_mul, add_zero]

theorem homogeneous_d_one :
    ∀ W : R5, IsUnit5 W →
      (∃ U : R5, OnHomogeneous U 1 W) → InDualLine W := by
  intro W hW ⟨U, hcurve⟩
  have hW0 : (toR3 W).c0 ≠ 0 := by
    rw [isUnit5_iff] at hW
    simpa [toR3, red3, mod3_apply] using hW
  have hred := onHomogeneous_one_reduction U W hcurve
  by_cases hU : IsUnit5 U
  · have hU0 : (toR3 U).c0 ≠ 0 := by
      rw [isUnit5_iff] at hU
      simpa [toR3, red3, mod3_apply] using hU
    obtain ⟨hWhead, hUhead, h1⟩ :=
      r3_hom_unit_first_tail_zero hW0 hU0 hred
    obtain ⟨ε, hε, y, hy⟩ := unit_decomp hU
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hε
    rcases hε with rfl | rfl
    · rw [hy, map_mul, map_one, one_mul, map_add, map_one, map_mul] at hUhead
      change (R3.add R3.one (R3.mul (toR3 pi5) (toR3 y))).c0 = 2 at hUhead
      simp [R3.add, R3.one, R3.mul] at hUhead
      have hpi0 : (toR3 pi5).c0 = 0 := by rfl
      rw [hpi0] at hUhead
      simp only [zero_mul, add_zero] at hUhead
      exact False.elim ((show (1 : ZMod 3) ≠ 2 by decide) hUhead)
    · rw [hy] at hcurve
      simp only [neg_one_mul] at hcurve
      unfold OnHomogeneous at hcurve
      simp only [mul_one, one_pow] at hcurve
      rcases W with ⟨a, b, c⟩
      rcases y with ⟨p, q, r⟩
      have ha0 : mod3 a = 2 := by
        simpa [toR3] using hWhead
      have hb0 : mod3 b = 0 := by
        simpa [toR3] using h1
      have hcubeNeg :
          (-(1 + pi5 * (⟨p, q, r⟩ : R5))) ^ 3 =
            -cubeForm (mod3 p) := by
        calc
          (-(1 + pi5 * (⟨p, q, r⟩ : R5))) ^ 3 =
              -(1 + pi5 * (⟨p, q, r⟩ : R5)) ^ 3 := by ring
          _ = -cubeForm ((p.val : Nat) : ZMod 3) := by rw [cube_image]
          _ = -cubeForm (mod3 p) := by rw [mod3_apply]
      rw [hcubeNeg] at hcurve
      have heq := congrArg R5.c1 hcurve
      rw [r5_mul_c1] at heq
      simp only [sub_eq_add_neg, r5_add_c0, r5_add_c1,
        r5_add_c2, r5_neg_c0, r5_neg_c1, r5_neg_c2,
        three_mul_neg_principal_c0, three_mul_neg_principal_c1,
        three_mul_neg_principal_c2, r5_two_c0, r5_two_c1,
        r5_two_c2, cubeForm] at heq
      have ha := zmod9_decomp a
      have hb := zmod9_decomp b
      rw [ha0] at ha
      rw [hb0] at hb
      rw [lift3_two] at ha
      rw [lift3_zero, zero_add] at hb
      have hp := three_mul_eq_three_lift_mod3 p
      have hpneg : (-3 : ZMod 9) * p = -3 * lift3 (mod3 p) := by
        calc
          (-3 : ZMod 9) * p = -(3 * p) := by ring
          _ = -(3 * lift3 (mod3 p)) := by rw [hp]
          _ = -3 * lift3 (mod3 p) := by ring
      rw [ha, hb, hpneg] at heq
      have h9 : (9 : ZMod 9) = 0 := by decide
      simp only [add_zero, neg_zero] at heq
      have hc9 : 3 * lift3 (c * c) = 0 := by
        linear_combination heq -
          (3 * lift3 (high9 b) +
            2 * lift3 (high9 a) * lift3 (high9 b) +
            lift3 (high9 a) * lift3 (mod3 p) +
            lift3 (mod3 p)) * h9
      have hcSq : c * c = 0 := by
        apply (show Function.Injective (fun z : ZMod 3 => 3 * lift3 z) by
          intro x z hxz
          revert x z
          decide)
        simpa [lift3] using hc9
      have hc : c = 0 := mul_self_eq_zero.mp hcSq
      apply inDualLine_of_reduction_tail_zero ⟨a, b, c⟩ hW h1
      simpa [toR3] using hc
  · have hU0 : (toR3 U).c0 = 0 := by
      rw [isUnit5_iff] at hU
      simp only [not_not] at hU
      simpa [toR3, red3, mod3_apply] using hU
    rw [hU0] at hred
    have hz : (⟨0, 0, 0⟩ : R3) = 0 := rfl
    rw [hz] at hred
    obtain ⟨h1, h2⟩ := r3_hom_zero_tail_zero hW0 hred
    exact inDualLine_of_reduction_tail_zero W hW h1 h2

/-! ## A nonunit denominator -/

theorem homogeneous_nonunit_d_rep_coordinates :
    ∀ i j k : F3, ∀ U D : R5,
      IsUnit5 U → ¬IsUnit5 D →
      OnHomogeneous U D (unitRep i j k) → i = 0 ∧ j = 0 := by
  intro i j k U D hU hD hcurve
  have hU0 : (toR3 U).c0 ≠ 0 := by
    rw [isUnit5_iff] at hU
    simpa [toR3, red3, mod3_apply] using hU
  have hD0 : (toR3 D).c0 = 0 := by
    rw [isUnit5_iff] at hD
    simp only [not_not] at hD
    simpa [toR3, red3, mod3_apply] using hD
  have hmap := congrArg toR3 hcurve
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat] at hmap
  rw [r3_cube (toR3 U), r3_cube (toR3 D)] at hmap
  rw [hD0] at hmap
  have hz : (⟨0, 0, 0⟩ : R3) = 0 := rfl
  rw [hz] at hmap
  have hsq : toR3 (unitRep i j k) * toR3 (unitRep i j k) =
      (⟨(toR3 U).c0, 0, 0⟩ : R3) := by
    simpa [three_r3] using hmap
  have hW0 : (toR3 (unitRep i j k)).c0 ≠ 0 := by
    intro hzero
    have hc0 := congrArg R3.c0 hsq
    change (toR3 (unitRep i j k)).c0 *
      (toR3 (unitRep i j k)).c0 = (toR3 U).c0 at hc0
    rw [hzero] at hc0
    simp at hc0
    exact hU0 hc0.symm
  obtain ⟨h1, h2⟩ := r3_sq_tail_zero hW0 hsq
  exact unitRep_reduction_tail_zero i j k h1 h2

/-! ## The positive-valuation chart -/

def OnScaledOne (U D W : R5) : Prop :=
  W * (pi5 ^ 3 * W - 3 * pi5 * U * D + 2 * D ^ 3) = U ^ 3

instance (U D W : R5) : Decidable (OnScaledOne U D W) := by
  unfold OnScaledOne
  infer_instance

theorem scaled_one_d_one :
    ∀ W : R5, IsUnit5 W →
      (∃ U : R5, IsUnit5 U ∧ OnScaledOne U 1 W) → InDualLine W := by
  intro W hW ⟨U, hU, hcurve⟩
  have hmap := congrArg toR3 hcurve
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat] at hmap
  rw [r3_cube (toR3 pi5), r3_cube (toR3 U)] at hmap
  have hpi0 : (toR3 pi5).c0 = 0 := by rfl
  rw [hpi0] at hmap
  have hz : (⟨0, 0, 0⟩ : R3) = 0 := rfl
  rw [hz] at hmap
  have hone : toR3 (1 : R5) = 1 := map_one toR3
  rw [hone] at hmap
  have hred : toR3 W * 2 = (⟨(toR3 U).c0, 0, 0⟩ : R3) := by
    simpa [three_r3] using hmap
  have h1 : (toR3 W).c1 = 0 := by
    have heq := congrArg R3.c1 hred
    change (R3.mul (toR3 W) (R3.add R3.one R3.one)).c1 = 0 at heq
    simp only [R3.mul, R3.add, R3.one, mul_zero, add_zero, mul_add,
      mul_one] at heq
    have htwo : (2 : ZMod 3) ≠ 0 := by decide
    exact (mul_eq_zero.mp (by simpa [two_mul] using heq)).resolve_left htwo
  have h2 : (toR3 W).c2 = 0 := by
    have heq := congrArg R3.c2 hred
    change (R3.mul (toR3 W) (R3.add R3.one R3.one)).c2 = 0 at heq
    simp only [R3.mul, R3.add, R3.one, mul_zero, add_zero, mul_add,
      mul_one] at heq
    have htwo : (2 : ZMod 3) ≠ 0 := by decide
    exact (mul_eq_zero.mp (by simpa [two_mul] using heq)).resolve_left htwo
  exact inDualLine_of_reduction_tail_zero W hW h1 h2

end MazurProof.N18RouteC.LocalThree
