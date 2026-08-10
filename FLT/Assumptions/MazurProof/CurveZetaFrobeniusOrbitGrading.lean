import FLT.Assumptions.MazurProof.CurveZetaPointOrbitClassification
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Closed points from Frobenius orbits

Let `σ` be a permutation of a finite geometric point set.  A closed point of
degree `d` is an orbit of points whose least positive `σ`-period is exactly
`d`.  This file constructs that quotient and proves the structural orbit
decomposition

`{points of exact period d} ≃ {closed points of degree d} × Fin d`.

The second factor records a Frobenius position inside the orbit.  Combining
the decompositions over the positive divisors of `k` identifies points fixed
by `σ^[k]` with the intrinsic degree-`k` ghost slots used by the marked
effective-divisor recurrence.  Thus the usual closed-point Euler
classification is obtained from an actual Frobenius action, not from a
cardinality equality.
-/

namespace MazurProof.CurveZetaFrobeniusOrbitGrading

open CurveZetaEffectiveDivisors
open CurveZetaMarkedDivisors
open CurveZetaPointOrbitClassification
open Function

variable {X : Type*}

/-! ## Exact-period points and their orbit relation -/

/-- Points whose least positive period under `σ` is exactly `d`. -/
def ExactPeriodicPoint (σ : Equiv.Perm X) (d : ℕ) :=
  {x : X // minimalPeriod σ x = d}

/-- An exact-period point is periodic whenever its prescribed period is
positive. -/
theorem exactPeriodicPoint_mem_periodicPts
    (σ : Equiv.Perm X) {d : ℕ} (hd : 0 < d)
    (x : ExactPeriodicPoint σ d) : x.1 ∈ periodicPts σ := by
  rw [← minimalPeriod_pos_iff_mem_periodicPts, x.2]
  exact hd

/-- Iterating an exact-period point by its prescribed period returns the
point. -/
theorem exactPeriodicPoint_iterate
    (σ : Equiv.Perm X) {d : ℕ} (x : ExactPeriodicPoint σ d) :
    σ^[d] x.1 = x.1 := by
  simpa only [x.2] using
    (iterate_minimalPeriod (f := (σ : X → X)) (x := x.1))

/-- Two exact-period points lie in the same orbit if one is an iterate of
the other at a position strictly below the common period. -/
def SameExactOrbit (σ : Equiv.Perm X) (d : ℕ)
    (x y : ExactPeriodicPoint σ d) : Prop :=
  ∃ i : Fin d, σ^[i.1] x.1 = y.1

/-- Every positive-period point lies in its own exact orbit. -/
theorem sameExactOrbit_refl
    (σ : Equiv.Perm X) {d : ℕ} (hd : 0 < d)
    (x : ExactPeriodicPoint σ d) : SameExactOrbit σ d x x := by
  exact ⟨⟨0, hd⟩, rfl⟩

/-- Moving backwards around a finite exact orbit supplies symmetry of the
orbit relation. -/
theorem sameExactOrbit_symm
    (σ : Equiv.Perm X) {d : ℕ} (hd : 0 < d)
    {x y : ExactPeriodicPoint σ d} :
    SameExactOrbit σ d x y → SameExactOrbit σ d y x := by
  rintro ⟨i, hi⟩
  by_cases hi0 : i.1 = 0
  · refine ⟨⟨0, hd⟩, ?_⟩
    simpa [hi0] using hi.symm
  · let j : Fin d :=
      ⟨d - i.1, Nat.sub_lt hd (Nat.zero_lt_of_ne_zero hi0)⟩
    refine ⟨j, ?_⟩
    change σ^[d - i.1] y.1 = x.1
    rw [← hi, ← iterate_add_apply]
    rw [Nat.sub_add_cancel (Nat.le_of_lt i.2)]
    exact exactPeriodicPoint_iterate σ x

/-- Adding two orbit positions modulo the exact period supplies transitivity
of the orbit relation. -/
theorem sameExactOrbit_trans
    (σ : Equiv.Perm X) {d : ℕ} (hd : 0 < d)
    {x y z : ExactPeriodicPoint σ d} :
    SameExactOrbit σ d x y → SameExactOrbit σ d y z →
      SameExactOrbit σ d x z := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  let k : Fin d := ⟨(j.1 + i.1) % d, Nat.mod_lt _ hd⟩
  refine ⟨k, ?_⟩
  change σ^[(j.1 + i.1) % d] x.1 = z.1
  calc
    σ^[(j.1 + i.1) % d] x.1 = σ^[j.1 + i.1] x.1 := by
      have h := iterate_mod_minimalPeriod_eq
        (f := (σ : X → X)) (x := x.1) (n := j.1 + i.1)
      rw [x.2] at h
      exact h
    _ = σ^[j.1] (σ^[i.1] x.1) := iterate_add_apply σ j.1 i.1 x.1
    _ = z.1 := by rw [hi, hj]

/-- The exact-orbit relation as a quotient setoid. -/
def sameExactOrbitSetoid
    (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d) :
    Setoid (ExactPeriodicPoint σ d) where
  r := SameExactOrbit σ d
  iseqv := ⟨sameExactOrbit_refl σ hd,
    @sameExactOrbit_symm X σ d hd,
    @sameExactOrbit_trans X σ d hd⟩

/-! ## Closed orbit classes and positions -/

/-- Frobenius orbit classes of exact period `d`. -/
def OrbitClass (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d) :=
  Quotient (sameExactOrbitSetoid σ d hd)

/-- Send an exact-period point to its orbit class. -/
def orbitClassMk
    (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d)
    (x : ExactPeriodicPoint σ d) : OrbitClass σ d hd :=
  @Quotient.mk _ (sameExactOrbitSetoid σ d hd) x

/-- Exact orbit classes are finite quotients of the finite point set. -/
noncomputable instance orbitClassFinite
    [Fintype X] (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d) :
    Finite (OrbitClass σ d hd) := by
  haveI : Finite (ExactPeriodicPoint σ d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Finite.of_surjective (orbitClassMk σ d hd) (by
    intro c
    exact ⟨@Quotient.out _ (sameExactOrbitSetoid σ d hd) c,
      Quotient.out_eq c⟩)

/-- Choose one geometric point representing an orbit class.  The choice is
used only to number positions; all downstream statements are independent of
the chosen representative. -/
noncomputable def orbitRepresentative
    (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d)
    (c : OrbitClass σ d hd) : ExactPeriodicPoint σ d :=
  @Quotient.out _ (sameExactOrbitSetoid σ d hd) c

/-- The chosen representative belongs to the class it represents. -/
theorem orbitRepresentative_class
    (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d)
    (c : OrbitClass σ d hd) :
    orbitClassMk σ d hd (orbitRepresentative σ d hd c) = c :=
  Quotient.out_eq c

/-- The unique position below `d` that moves the chosen class representative
to an exact-period point. -/
noncomputable def orbitPosition
    (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d)
    (x : ExactPeriodicPoint σ d) : Fin d :=
  Classical.choose (show SameExactOrbit σ d
      (orbitRepresentative σ d hd (orbitClassMk σ d hd x)) x from
    Quotient.exact (orbitRepresentative_class σ d hd
      (orbitClassMk σ d hd x)))

/-- The selected orbit position really reaches the given exact-period
point. -/
theorem orbitPosition_spec
    (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d)
    (x : ExactPeriodicPoint σ d) :
    σ^[(orbitPosition σ d hd x).1]
        (orbitRepresentative σ d hd (orbitClassMk σ d hd x)).1 = x.1 :=
  Classical.choose_spec (show SameExactOrbit σ d
      (orbitRepresentative σ d hd (orbitClassMk σ d hd x)) x from
    Quotient.exact (orbitRepresentative_class σ d hd
      (orbitClassMk σ d hd x)))

/-- Recover the point at a selected position in an exact orbit. -/
noncomputable def orbitPoint
    (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d)
    (c : OrbitClass σ d hd) (i : Fin d) : ExactPeriodicPoint σ d := by
  refine ⟨σ^[i.1] (orbitRepresentative σ d hd c).1, ?_⟩
  rw [minimalPeriod_apply_iterate
    (exactPeriodicPoint_mem_periodicPts σ hd
      (orbitRepresentative σ d hd c))]
  exact (orbitRepresentative σ d hd c).2

/-- An exact-period point is exactly an orbit class together with one of its
`d` Frobenius positions. -/
noncomputable def exactPeriodicPointEquivOrbitClassProd
    (σ : Equiv.Perm X) (d : ℕ) (hd : 0 < d) :
    ExactPeriodicPoint σ d ≃ OrbitClass σ d hd × Fin d where
  toFun x := ⟨orbitClassMk σ d hd x, orbitPosition σ d hd x⟩
  invFun p := orbitPoint σ d hd p.1 p.2
  left_inv x := by
    apply Subtype.ext
    exact orbitPosition_spec σ d hd x
  right_inv p := by
    rcases p with ⟨c, i⟩
    have hclass : orbitClassMk σ d hd (orbitPoint σ d hd c i) = c := by
      calc
        orbitClassMk σ d hd (orbitPoint σ d hd c i) =
            orbitClassMk σ d hd (orbitRepresentative σ d hd c) := by
          apply Quotient.sound
          exact sameExactOrbit_symm σ hd ⟨i, rfl⟩
        _ = c := orbitRepresentative_class σ d hd c
    apply Prod.ext
    · exact hclass
    · apply Fin.ext
      apply (iterate_eq_iterate_iff_of_lt_minimalPeriod
        (f := (σ : X → X))
        (x := (orbitRepresentative σ d hd c).1)
        (m := (orbitPosition σ d hd (orbitPoint σ d hd c i)).1)
        (n := i.1)
        (by
          simp [(orbitRepresentative σ d hd c).2])
        (by
          simp [(orbitRepresentative σ d hd c).2])).mp
      have hspec := orbitPosition_spec σ d hd (orbitPoint σ d hd c i)
      rw [hclass] at hspec
      simpa only [orbitPoint] using hspec

/-! ## The closed-point grading of a finite permutation -/

universe u

variable {Y : Type u}

/-- Closed points of positive degree are exact-period orbit classes.  Degree
zero is a universe-lifted empty type, as residue degrees are positive. -/
def OrbitClosed (σ : Equiv.Perm Y) : ℕ → Type u
  | 0 => ULift Empty
  | d + 1 => OrbitClass σ (d + 1) (Nat.succ_pos d)

/-- Each degree contains finitely many orbit classes. -/
noncomputable instance orbitClosedFinite [Fintype Y]
    (σ : Equiv.Perm Y) (d : ℕ) : Finite (OrbitClosed σ d) := by
  cases d with
  | zero =>
      exact Finite.of_injective ULift.down (by
        intro x y h
        cases x
        cases y
        cases h
        rfl)
  | succ d => exact orbitClassFinite σ (d + 1) (Nat.succ_pos d)

/-- There are no degree-zero orbit classes. -/
instance orbitClosedZeroIsEmpty (σ : Equiv.Perm Y) :
    IsEmpty (OrbitClosed σ 0) := ⟨fun x => Empty.elim x.down⟩

/-- The locally finite grading of closed points arising from a finite
permutation. -/
noncomputable def orbitClosedPointGrading [Fintype Y]
    (σ : Equiv.Perm Y) : ClosedPointGrading where
  Closed := OrbitClosed σ
  finite_closed := orbitClosedFinite σ
  empty_degree_zero := orbitClosedZeroIsEmpty σ

/-! ## Fixed points as closed-point slots -/

/-- Positive divisors of `k`, which are exactly the possible least periods
of points fixed by the `k`-th iterate. -/
abbrev PositiveDivisor (k : ℕ) := {d : ℕ // 0 < d ∧ d ∣ k}

/-- Points fixed by the `k`-th iterate of a permutation. -/
def FixedByIterate (σ : Equiv.Perm Y) (k : ℕ) :=
  {x : Y // σ^[k] x = x}

/-- Forgetting the least-period index is injective on the sigma type of
exact-period points, because the point itself determines its least period. -/
def sigmaExactVal (σ : Equiv.Perm Y) (k : ℕ) :
    (Σ d : PositiveDivisor k, ExactPeriodicPoint σ d.1) → Y :=
  fun x => x.2.1

/-- The geometric point determines both its exact-period proof and its
positive-divisor index. -/
theorem sigmaExactVal_injective (σ : Equiv.Perm Y) (k : ℕ) :
    Function.Injective (sigmaExactVal σ k) := by
  rintro ⟨d, x⟩ ⟨e, y⟩ hxy
  have hde : d = e := by
    apply Subtype.ext
    calc
      d.1 = minimalPeriod σ x.1 := x.2.symm
      _ = minimalPeriod σ y.1 := congrArg (minimalPeriod σ) hxy
      _ = e.1 := y.2
  apply Sigma.ext hde
  apply (Subtype.heq_iff_coe_eq (fun z => by
    rw [congrArg Subtype.val hde])).2
  exact hxy

/-- A point fixed by `σ^[k]` has a positive least period dividing `k`.
Conversely, every exact-period point for a positive divisor of `k` is fixed
by the `k`-th iterate. -/
noncomputable def fixedByIterateEquivSigmaExact
    (σ : Equiv.Perm Y) (k : ℕ) (hk : 0 < k) :
    FixedByIterate σ k ≃
      Σ d : PositiveDivisor k, ExactPeriodicPoint σ d.1 where
  toFun x := by
    have hper : IsPeriodicPt σ k x.1 := x.2
    exact ⟨⟨minimalPeriod σ x.1, hper.minimalPeriod_pos hk,
      hper.minimalPeriod_dvd⟩, x.1, rfl⟩
  invFun x := ⟨x.2.1, by
    apply isPeriodicPt_iff_minimalPeriod_dvd.mpr
    simpa only [x.2.2] using x.1.2.2⟩
  left_inv x := rfl
  right_inv x := sigmaExactVal_injective σ k rfl

/-- At every positive divisor of `k`, the exact-period orbit decomposition
is definitionally the corresponding component of the orbit grading. -/
noncomputable def exactPeriodicPointEquivClosedProd [Fintype Y]
    (σ : Equiv.Perm Y) {k : ℕ} (d : PositiveDivisor k) :
    ExactPeriodicPoint σ d.1 ≃ OrbitClosed σ d.1 × Fin d.1 := by
  rcases d with ⟨_ | d, hd, hdvd⟩
  · exact False.elim (Nat.lt_asymm hd hd)
  · exact exactPeriodicPointEquivOrbitClassProd σ (d + 1) (Nat.succ_pos d)

/-- Fixed points decompose into a closed orbit of some degree dividing `k`
and one Frobenius position in that orbit. -/
noncomputable def fixedByIterateEquivClosedSlots [Fintype Y]
    (σ : Equiv.Perm Y) (k : ℕ) (hk : 0 < k) :
    FixedByIterate σ k ≃
      Σ d : PositiveDivisor k, OrbitClosed σ d.1 × Fin d.1 :=
  (fixedByIterateEquivSigmaExact σ k hk).trans
    (Equiv.sigmaCongrRight fun d => exactPeriodicPointEquivClosedProd σ d)

/-! ## Comparison with intrinsic marked-divisor ghost slots -/

/-- The quotient `k / d`, selected from the divisibility proof carried by a
positive divisor. -/
noncomputable def divisorQuotient {k : ℕ} (d : PositiveDivisor k) : ℕ :=
  Classical.choose d.2.2

/-- The selected quotient really multiplies `d` to `k`. -/
theorem divisorQuotient_spec {k : ℕ} (d : PositiveDivisor k) :
    k = d.1 * divisorQuotient d :=
  Classical.choose_spec d.2.2

/-- Convert a closed orbit and its position to an intrinsic ghost slot.  The
copy count is the unique positive quotient `k / d`. -/
noncomputable def closedSlotsToExactGhost [Fintype Y]
    (σ : Equiv.Perm Y) (k : ℕ) (hk : 0 < k) :
    (Σ d : PositiveDivisor k, OrbitClosed σ d.1 × Fin d.1) →
      CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        (orbitClosedPointGrading σ) k := by
  rintro ⟨d, c, i⟩
  have hqpos : 0 < divisorQuotient d := by
    by_contra hq
    have hqzero : divisorQuotient d = 0 := Nat.eq_zero_of_not_pos hq
    have : ¬0 < k := by simp [divisorQuotient_spec d, hqzero]
    exact this hk
  have hqmul : divisorQuotient d * d.1 = k := by
    rw [Nat.mul_comm, ← divisorQuotient_spec d]
  have hqle : divisorQuotient d ≤ k := by
    calc
      divisorQuotient d = divisorQuotient d * 1 := by simp
      _ ≤ divisorQuotient d * d.1 :=
        Nat.mul_le_mul_left (divisorQuotient d) d.2.1
      _ = k := hqmul
  let x : (orbitClosedPointGrading σ).AtomLE k :=
    ⟨⟨d.1, c⟩, Nat.le_of_dvd hk d.2.2⟩
  let rfin : Fin (k + 1) :=
    ⟨divisorQuotient d, Nat.lt_succ_of_le hqle⟩
  let r : CurveZetaMarkedDivisors.ClosedPointGrading.ExactCopies
      (orbitClosedPointGrading σ) k x :=
    ⟨rfin, hqpos, hqmul⟩
  exact ⟨x, r, i⟩

/-- Read the orbit degree, orbit class, and position from an intrinsic ghost
slot.  Its exact-copy equation proves that the orbit degree divides `k`. -/
noncomputable def exactGhostToClosedSlots [Fintype Y]
    (σ : Equiv.Perm Y) (k : ℕ) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        (orbitClosedPointGrading σ) k →
      Σ d : PositiveDivisor k, OrbitClosed σ d.1 × Fin d.1 := by
  rintro ⟨x, r, i⟩
  let d : PositiveDivisor k :=
    ⟨x.1.1, (orbitClosedPointGrading σ).atomDegree_pos x.1,
      ⟨r.1.1, r.2.2.symm.trans (Nat.mul_comm _ _)⟩⟩
  exact ⟨d, x.1.2, i⟩

/-- The orbit-slot description and the marked-divisor ghost-slot description
are equivalent.  Uniqueness of the copy count follows by cancellation
against the positive closed-point degree. -/
noncomputable def closedSlotsEquivExactGhost [Fintype Y]
    (σ : Equiv.Perm Y) (k : ℕ) (hk : 0 < k) :
    (Σ d : PositiveDivisor k, OrbitClosed σ d.1 × Fin d.1) ≃
      CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        (orbitClosedPointGrading σ) k where
  toFun := closedSlotsToExactGhost σ k hk
  invFun := exactGhostToClosedSlots σ k
  left_inv p := by
    rcases p with ⟨d, c, i⟩
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · rfl
  right_inv s := by
    apply CurveZetaMarkedDivisors.ClosedPointGrading.exactGhostCoordinates_injective
      (orbitClosedPointGrading σ) k
    rcases s with ⟨x, r, i⟩
    let d : PositiveDivisor k :=
      ⟨x.1.1, (orbitClosedPointGrading σ).atomDegree_pos x.1,
        ⟨r.1.1, r.2.2.symm.trans (Nat.mul_comm _ _)⟩⟩
    change (x.1, divisorQuotient d, i.1) =
      (x.1, r.1.1, i.1)
    simp only [Prod.mk.injEq, true_and]
    constructor
    · apply Nat.mul_right_cancel
        ((orbitClosedPointGrading σ).atomDegree_pos x.1)
      calc
        divisorQuotient d * x.1.1 = x.1.1 * divisorQuotient d :=
          Nat.mul_comm _ _
        _ = k := (divisorQuotient_spec d).symm
        _ = r.1.1 * x.1.1 := r.2.2.symm
    · trivial

/-- For every positive `k`, points fixed by `σ^[k]` are exactly the
intrinsic degree-`k` ghost slots of the orbit closed-point grading. -/
noncomputable def fixedByIterateEquivExactGhost [Fintype Y]
    (σ : Equiv.Perm Y) (k : ℕ) (hk : 0 < k) :
    FixedByIterate σ k ≃
      CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        (orbitClosedPointGrading σ) k :=
  (fixedByIterateEquivClosedSlots σ k hk).trans
    (closedSlotsEquivExactGhost σ k hk)

/-! ## Packaging selected semantic point types -/

/-- A selected semantic point type is realized as the fixed points of the
corresponding Frobenius iterate.  The positivity field records that all
selected extension degrees are genuine positive residue degrees. -/
structure FixedPointRealizationOn [Fintype Y]
    (σ : Equiv.Perm Y)
    (Index : Type*)
    (exponent : Index → ℕ)
    (pointType : Index → Type*) where
  /-- Semantic points over the selected extension are exactly the geometric
  points fixed by the corresponding Frobenius iterate. -/
  realize : ∀ i, pointType i ≃ FixedByIterate σ (exponent i)
  /-- Every selected extension exponent is positive. -/
  exponent_pos : ∀ i, 0 < exponent i

namespace FixedPointRealizationOn

variable [Fintype Y]
variable {σ : Equiv.Perm Y}
variable {Index : Type*} {exponent : Index → ℕ}
variable {pointType : Index → Type*}

/-- A fixed-point realization supplies the honest closed-point orbit
classification required by the Euler recurrence. -/
noncomputable def pointOrbitClassification
    (R : FixedPointRealizationOn σ Index exponent pointType) :
    PointOrbitClassificationOn (orbitClosedPointGrading σ)
      Index exponent pointType where
  classify i := (R.realize i).trans
    (fixedByIterateEquivExactGhost σ (exponent i) (R.exponent_pos i))

end FixedPointRealizationOn

end MazurProof.CurveZetaFrobeniusOrbitGrading
