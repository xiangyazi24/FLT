import FLT.Assumptions.MazurProof.CurveZetaEffectiveDivisors
import FLT.Assumptions.MazurProof.CurveZetaEulerRecurrence
import Mathlib.Data.Finite.Sigma

/-!
# Marked effective divisors

The Euler recurrence is a double-counting theorem.  On one side, mark one
unit of residue degree inside an effective divisor of degree `n`.  A closed
point `x` occurring with multiplicity `m` contributes `m * deg(x)` marks, so
every divisor contributes exactly `n` marks.

This module proves that first cardinality identity without enumeration.  The
next layer re-encodes the same mark by the number of copies of `x` removed
from the divisor and obtains the ghost/Euler sum.
-/

namespace MazurProof.CurveZetaMarkedDivisors

open CurveZetaEffectiveDivisors
open scoped BigOperators

namespace ClosedPointGrading

variable (C : ClosedPointGrading)

/-- A degree-`n` effective divisor with a marked occurrence of a closed point
and a marked unit among that point's residue degree. -/
def MarkedEffDiv (n : ℕ) :=
  Σ D : C.EffDivOfDegree n,
    Σ x : D.1.support,
      Fin (D.1 x.1) × Fin (C.atomDegree x.1)

/-- The inner marks over one divisor have cardinality equal to its weighted
degree. -/
theorem card_marks_over_divisor (n : ℕ) (D : C.EffDivOfDegree n) :
    Nat.card (Σ x : D.1.support,
      Fin (D.1 x.1) × Fin (C.atomDegree x.1)) = n := by
  classical
  rw [Nat.card_sigma]
  simp only [Nat.card_prod, Nat.card_fin]
  rw [← Finset.sum_subtype D.1.support (by simp)
    (fun x => D.1 x * C.atomDegree x)]
  simpa only [CurveZetaEffectiveDivisors.ClosedPointGrading.divDegree,
    Finsupp.sum] using D.2

/-- Every degree-`n` effective divisor has exactly `n` marks.  Consequently
the marked-divisor type has cardinality `n * A_n`. -/
theorem card_markedEffDiv (n : ℕ) :
    Nat.card (MarkedEffDiv C n) = n * C.effectiveCount n := by
  classical
  letI := Fintype.ofFinite (C.EffDivOfDegree n)
  unfold MarkedEffDiv
  rw [Nat.card_sigma]
  simp_rw [card_marks_over_divisor C n]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    CurveZetaEffectiveDivisors.ClosedPointGrading.effectiveCount,
    Nat.card_eq_fintype_card]
  simp only [Nat.cast_id, mul_comm]

/-! ## Removing the marked copies -/

/-- Positive copy counts of a bounded closed point whose total contribution
does not exceed `n`.  The `Fin (n+1)` carrier makes this type finite without
enumerating any divisor. -/
def AdmissibleCopies (n : ℕ) (x : C.AtomLE n) :=
  {r : Fin (n + 1) // 1 ≤ r.1 ∧ r.1 * C.atomDegree x.1 ≤ n}

/-- Admissible copy counts are finite because they inject into
`Fin (n+1)`. -/
instance admissibleCopiesFinite (n : ℕ) (x : C.AtomLE n) :
    Finite (AdmissibleCopies C n x) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- A chosen enumeration of the bounded closed points. -/
noncomputable instance atomLEFintype (n : ℕ) : Fintype (C.AtomLE n) :=
  Fintype.ofFinite (C.AtomLE n)

/-- A chosen enumeration of the admissible copy counts. -/
noncomputable instance admissibleCopiesFintype
    (n : ℕ) (x : C.AtomLE n) : Fintype (AdmissibleCopies C n x) :=
  Fintype.ofFinite (AdmissibleCopies C n x)

/-- Return data after removing `r` copies of a marked closed point.  The
residual divisor has degree `n-r*deg(x)`, and the final finite coordinate is
the marked unit of residue degree. -/
def MarkedReturnData (n : ℕ) :=
  Σ x : C.AtomLE n,
    Σ r : AdmissibleCopies C n x,
      Fin (C.atomDegree x.1) ×
        C.EffDivOfDegree (n - r.1.1 * C.atomDegree x.1)

/-- Convert a marked divisor to return data by removing `i+1` copies of its
marked closed point. -/
noncomputable def markedToReturn (n : ℕ) :
    MarkedEffDiv C n → MarkedReturnData C n := by
  intro M
  rcases M with ⟨D, x, i, t⟩
  have hdegree : C.divDegree D.1 ≤ n := Nat.le_of_eq D.2
  have hxDegree : C.atomDegree x.1 ≤ n :=
    C.atomDegree_le_of_mem_support D.1 n hdegree x.2
  let xb : C.AtomLE n := ⟨x.1, hxDegree⟩
  have hir : i.1 + 1 ≤ D.1 x.1 := i.2
  have hcoeff : D.1 x.1 ≤ n := C.coeff_le_of_divDegree_le D.1 n hdegree x.1
  let rfin : Fin (n + 1) := ⟨i.1 + 1, by omega⟩
  have hrContribution : rfin.1 * C.atomDegree xb.1 ≤ n := by
    calc
      rfin.1 * C.atomDegree xb.1 ≤ D.1 x.1 * C.atomDegree x.1 :=
        Nat.mul_le_mul_right _ hir
      _ ≤ C.divDegree D.1 := C.term_le_divDegree D.1 x.1
      _ = n := D.2
  have hrPositive : 1 ≤ rfin.1 := by
    dsimp only [rfin]
    exact Nat.succ_le_succ (Nat.zero_le i.1)
  let r : AdmissibleCopies C n xb :=
    ⟨rfin, hrPositive, hrContribution⟩
  refine ⟨xb, r, t, ?_⟩
  refine ⟨D.1 - Finsupp.single x.1 rfin.1, ?_⟩
  calc
    C.divDegree (D.1 - Finsupp.single x.1 rfin.1) =
        C.divDegree D.1 - rfin.1 * C.atomDegree x.1 :=
      C.divDegree_sub_single D.1 x.1 rfin.1 hir
    _ = n - r.1.1 * C.atomDegree xb.1 := by
      rw [D.2]

/-- Reinsert the removed copies and mark the last reinserted copy. -/
noncomputable def returnToMarked (n : ℕ) :
    MarkedReturnData C n → MarkedEffDiv C n := by
  intro R
  rcases R with ⟨x, r, t, E⟩
  let copies : ℕ := r.1.1
  have hcopies : 0 < copies := by
    dsimp only [copies]
    exact r.2.1
  let D₀ : C.EffDiv := E.1 + Finsupp.single x.1 copies
  have hdegree : C.divDegree D₀ = n := by
    dsimp [D₀]
    rw [C.divDegree_add, C.divDegree_single, E.2]
    exact Nat.sub_add_cancel r.2.2
  let D : C.EffDivOfDegree n := ⟨D₀, hdegree⟩
  have hxCoeff : D.1 x.1 = E.1 x.1 + copies := by
    simp [D, D₀]
  have hxSupport : x.1 ∈ D.1.support := by
    rw [Finsupp.mem_support_iff, hxCoeff]
    exact Nat.ne_of_gt (Nat.add_pos_right (E.1 x.1) hcopies)
  let xs : D.1.support := ⟨x.1, hxSupport⟩
  let i : Fin (D.1 xs.1) := ⟨copies - 1, by
    rw [hxCoeff]
    omega⟩
  exact ⟨D, xs, i, t⟩

/-- Forget the proof fields of a marked divisor while retaining all of its
mathematical coordinates.  Equality of these coordinates is sufficient to
recover equality of the original dependent sigma terms. -/
def markedEffDivCoordinates (n : ℕ) (M : MarkedEffDiv C n) :
    C.EffDiv × C.Atom × ℕ × ℕ :=
  (M.1.1, M.2.1.1, M.2.2.1.1, M.2.2.2.1)

/-- The proof-erasing coordinates of a marked divisor are injective. -/
theorem markedEffDivCoordinates_injective (n : ℕ) :
    Function.Injective (markedEffDivCoordinates C n) := by
  rintro ⟨⟨D, hD⟩, ⟨x, hx⟩, i, t⟩ ⟨⟨E, hE⟩, ⟨y, hy⟩, j, u⟩ h
  change (D, x, i.1, t.1) = (E, y, j.1, u.1) at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hDE, hxy, hij, htu⟩
  subst E
  subst y
  have hij' : i = j := Fin.ext hij
  have htu' : t = u := Fin.ext htu
  subst j
  subst u
  rfl

/-- Forget the proof fields of return data while retaining the atom, copy
count, residue slot, and residual divisor. -/
def markedReturnCoordinates (n : ℕ) (R : MarkedReturnData C n) :
    C.Atom × ℕ × ℕ × C.EffDiv :=
  (R.1.1, R.2.1.1.1, R.2.2.1.1, R.2.2.2.1)

/-- The proof-erasing coordinates of marked return data are injective. -/
theorem markedReturnCoordinates_injective (n : ℕ) :
    Function.Injective (markedReturnCoordinates C n) := by
  rintro ⟨⟨x, hx⟩, ⟨⟨r, hr⟩, hradm⟩, t, ⟨E, hE⟩⟩
    ⟨⟨y, hy⟩, ⟨⟨s, hs⟩, hsadm⟩, u, ⟨F, hF⟩⟩ h
  change (x, r, t.1, E) = (y, s, u.1, F) at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hxy, hrs, htu, hEF⟩
  subst y
  subst s
  subst F
  have htu' : t = u := Fin.ext htu
  subst u
  rfl

/-- Marking a divisor and recording the removed copies are equivalent finite
descriptions.  This is the bijective core of the Euler double count: the
forward map removes the copies through the marked level, while the inverse
reinserts exactly those copies. -/
noncomputable def markedEffDivEquivReturnData (n : ℕ) :
    MarkedEffDiv C n ≃ MarkedReturnData C n where
  toFun := markedToReturn C n
  invFun := returnToMarked C n
  left_inv := by
    rintro ⟨⟨D, hD⟩, x, i, t⟩
    have hir : i.1 + 1 ≤ D x.1 := i.2
    have hDiv :
        D - (Finsupp.single x.1 i.1 + Finsupp.single x.1 1) +
            (Finsupp.single x.1 i.1 + Finsupp.single x.1 1) = D := by
      ext y
      by_cases hy : y = x.1
      · subst y
        simp [Nat.sub_add_cancel hir]
      · simp [hy]
    apply markedEffDivCoordinates_injective C n
    simpa [markedEffDivCoordinates, markedToReturn, returnToMarked] using hDiv
  right_inv := by
    rintro ⟨x, r, t, E⟩
    have hr : r.1.1 - 1 + 1 = r.1.1 :=
      Nat.sub_add_cancel r.2.1
    have hremove :
        E.1 + Finsupp.single x.1 r.1.1 -
            Finsupp.single x.1 r.1.1 = E.1 :=
      C.add_single_sub_single E.1 x.1 r.1.1
    apply markedReturnCoordinates_injective C n
    simp [markedReturnCoordinates, markedToReturn, returnToMarked,
      hr, hremove]

/-! ## Grouping the return data by removed degree -/

/-- A bounded closed point together with an admissible positive number of
copies to remove. -/
abbrev CopyChoice (n : ℕ) :=
  Σ x : C.AtomLE n, AdmissibleCopies C n x

/-- The total degree removed by a copy choice, regarded as an index between
zero and `n`. -/
def copyContribution (n : ℕ) (p : CopyChoice C n) : Fin (n + 1) :=
  ⟨p.2.1.1 * C.atomDegree p.1.1,
    Nat.lt_succ_of_le p.2.2.2⟩

/-- A bounded ghost slot of degree `k` consists of a copy choice removing
exactly `k` degrees and one residue-degree position on its closed point. -/
def BoundedGhostSlot (n : ℕ) (k : Fin (n + 1)) :=
  Σ p : {p : CopyChoice C n // copyContribution C n p = k},
    Fin (C.atomDegree p.1.1.1)

/-- A contribution fiber is finite because it is a subtype of the finite
copy-choice type. -/
instance copyContributionFiberFinite (n : ℕ) (k : Fin (n + 1)) :
    Finite {p : CopyChoice C n // copyContribution C n p = k} :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The number of bounded ghost slots of removed degree `k`. -/
noncomputable def boundedGhostCount (n : ℕ) (k : Fin (n + 1)) : ℕ :=
  Nat.card (BoundedGhostSlot C n k)

/-- The cardinality of return data is the sum over copy choices of the
residue degree times the number of possible residual divisors. -/
theorem card_markedReturnData (n : ℕ) :
    Nat.card (MarkedReturnData C n) =
      ∑ p : CopyChoice C n,
        C.atomDegree p.1.1 *
          C.effectiveCount
            (n - (copyContribution C n p).1) := by
  classical
  unfold MarkedReturnData
  rw [Nat.card_sigma]
  simp_rw [Nat.card_sigma, Nat.card_prod, Nat.card_fin]
  simpa [CopyChoice, copyContribution,
    CurveZetaEffectiveDivisors.ClosedPointGrading.effectiveCount] using
    (Fintype.sum_sigma'
      (fun x (r : AdmissibleCopies C n x) =>
        C.atomDegree x.1 *
          C.effectiveCount
            (n - r.1.1 * C.atomDegree x.1))).symm

/-- A ghost count is the sum of the residue degrees over the copy choices in
its contribution fiber. -/
theorem boundedGhostCount_eq_degree_sum (n : ℕ) (k : Fin (n + 1)) :
    boundedGhostCount C n k =
      ∑ p : {p : CopyChoice C n // copyContribution C n p = k},
        C.atomDegree p.1.1.1 := by
  classical
  rw [boundedGhostCount, BoundedGhostSlot, Nat.card_sigma]
  simp only [Nat.card_fin]

/-- Grouping copy choices by their removed degree rewrites the return-data
sum as the ghost convolution. -/
theorem copyChoice_sum_eq_ghost_sum (n : ℕ) :
    (∑ p : CopyChoice C n,
        C.atomDegree p.1.1 *
          C.effectiveCount (n - (copyContribution C n p).1)) =
      ∑ k : Fin (n + 1),
        boundedGhostCount C n k * C.effectiveCount (n - k.1) := by
  classical
  calc
    (∑ p : CopyChoice C n,
        C.atomDegree p.1.1 *
          C.effectiveCount (n - (copyContribution C n p).1)) =
        ∑ k : Fin (n + 1),
          ∑ p : {p : CopyChoice C n // copyContribution C n p = k},
            C.atomDegree p.1.1.1 *
              C.effectiveCount
                (n - (copyContribution C n p.1).1) :=
      (Fintype.sum_fiberwise (copyContribution C n)
        (fun p => C.atomDegree p.1.1 *
          C.effectiveCount
            (n - (copyContribution C n p).1))).symm
    _ = ∑ k : Fin (n + 1),
          boundedGhostCount C n k * C.effectiveCount (n - k.1) := by
      apply Fintype.sum_congr
      intro k
      rw [boundedGhostCount_eq_degree_sum, Finset.sum_mul]
      apply Fintype.sum_congr
      intro p
      rw [p.2]

/-- The marked-divisor equivalence proves the bounded Euler recurrence as a
finite double count.  No Euler product, logarithm, or recurrence hypothesis
is used. -/
theorem boundedEulerRecurrence (n : ℕ) :
    n * C.effectiveCount n =
      ∑ k : Fin (n + 1),
        boundedGhostCount C n k * C.effectiveCount (n - k.1) := by
  calc
    n * C.effectiveCount n = Nat.card (MarkedEffDiv C n) :=
      (card_markedEffDiv C n).symm
    _ = Nat.card (MarkedReturnData C n) :=
      Nat.card_congr (markedEffDivEquivReturnData C n)
    _ = ∑ p : CopyChoice C n,
          C.atomDegree p.1.1 *
            C.effectiveCount (n - (copyContribution C n p).1) :=
      card_markedReturnData C n
    _ = ∑ k : Fin (n + 1),
          boundedGhostCount C n k * C.effectiveCount (n - k.1) :=
      copyChoice_sum_eq_ghost_sum C n

/-! ## Removing the coefficient cutoff from ghost slots -/

/-- Positive copy counts whose contribution is exactly `k`. -/
def ExactCopies (k : ℕ) (x : C.AtomLE k) :=
  {r : Fin (k + 1) //
    1 ≤ r.1 ∧ r.1 * C.atomDegree x.1 = k}

/-- Exact copy counts are finite because they inject into `Fin (k+1)`. -/
instance exactCopiesFinite (k : ℕ) (x : C.AtomLE k) :
    Finite (ExactCopies C k x) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- A chosen enumeration of exact copy counts. -/
noncomputable instance exactCopiesFintype (k : ℕ) (x : C.AtomLE k) :
    Fintype (ExactCopies C k x) :=
  Fintype.ofFinite (ExactCopies C k x)

/-- The intrinsic ghost slots of total contribution `k`.  Retaining the
positive copy count makes cutoff-independence an explicit finite equivalence,
without division by the closed-point degree. -/
def ExactGhostSlot (k : ℕ) :=
  Σ x : C.AtomLE k,
    Σ _r : ExactCopies C k x,
      Fin (C.atomDegree x.1)

/-- The intrinsic closed-point ghost coefficient of degree `k`. -/
noncomputable def ghostCount (k : ℕ) : ℕ :=
  Nat.card (ExactGhostSlot C k)

/-- Shrink a bounded ghost slot to its intrinsic contribution cutoff. -/
noncomputable def boundedGhostToExact
    (n : ℕ) (k : Fin (n + 1)) :
    BoundedGhostSlot C n k → ExactGhostSlot C k.1 := by
  rintro ⟨⟨⟨x, r⟩, hcontribution⟩, t⟩
  have hproduct : r.1.1 * C.atomDegree x.1 = k.1 := by
    exact congrArg Fin.val hcontribution
  have hxk : C.atomDegree x.1 ≤ k.1 := by
    calc
      C.atomDegree x.1 = 1 * C.atomDegree x.1 := by simp
      _ ≤ r.1.1 * C.atomDegree x.1 :=
        Nat.mul_le_mul_right _ r.2.1
      _ = k.1 := hproduct
  let xk : C.AtomLE k.1 := ⟨x.1, hxk⟩
  have hrk : r.1.1 ≤ k.1 := by
    calc
      r.1.1 = r.1.1 * 1 := by simp
      _ ≤ r.1.1 * C.atomDegree x.1 :=
        Nat.mul_le_mul_left _ (C.atomDegree_pos x.1)
      _ = k.1 := hproduct
  let rk : Fin (k.1 + 1) := ⟨r.1.1, Nat.lt_succ_of_le hrk⟩
  let re : ExactCopies C k.1 xk :=
    ⟨rk, r.2.1, hproduct⟩
  exact ⟨xk, re, t⟩

/-- Extend an intrinsic ghost slot to any ambient coefficient cutoff that
contains its contribution degree. -/
noncomputable def exactGhostToBounded
    (n : ℕ) (k : Fin (n + 1)) :
    ExactGhostSlot C k.1 → BoundedGhostSlot C n k := by
  rintro ⟨x, r, t⟩
  have hkn : k.1 ≤ n := Nat.le_of_lt_succ k.2
  let xn : C.AtomLE n := ⟨x.1, x.2.trans hkn⟩
  have hrn : r.1.1 < n + 1 :=
    lt_of_lt_of_le r.1.2 (Nat.succ_le_succ hkn)
  let rn : Fin (n + 1) := ⟨r.1.1, hrn⟩
  let rb : AdmissibleCopies C n xn :=
    ⟨rn, r.2.1, r.2.2.le.trans hkn⟩
  let p : CopyChoice C n := ⟨xn, rb⟩
  have hp : copyContribution C n p = k := by
    apply Fin.ext
    exact r.2.2
  exact ⟨⟨p, hp⟩, t⟩

/-- The atom, copy count, and residue position determine a bounded ghost
slot, independently of its proof fields. -/
def boundedGhostCoordinates
    (n : ℕ) (k : Fin (n + 1)) (s : BoundedGhostSlot C n k) :
    C.Atom × ℕ × ℕ :=
  (s.1.1.1.1, s.1.1.2.1.1, s.2.1)

/-- Proof-erasing bounded ghost coordinates are injective. -/
theorem boundedGhostCoordinates_injective
    (n : ℕ) (k : Fin (n + 1)) :
    Function.Injective (boundedGhostCoordinates C n k) := by
  rintro ⟨⟨⟨⟨x, hx⟩, ⟨⟨r, hrn⟩, hr⟩⟩, hp⟩, t⟩
    ⟨⟨⟨⟨y, hy⟩, ⟨⟨s, hsn⟩, hs⟩⟩, hq⟩, u⟩ h
  change (x, r, t.1) = (y, s, u.1) at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hxy, hrs, htu⟩
  subst y
  subst s
  have htu' : t = u := Fin.ext htu
  subst u
  rfl

/-- The atom, copy count, and residue position determine an intrinsic ghost
slot, independently of its proof fields. -/
def exactGhostCoordinates (k : ℕ) (s : ExactGhostSlot C k) :
    C.Atom × ℕ × ℕ :=
  (s.1.1, s.2.1.1.1, s.2.2.1)

/-- Proof-erasing intrinsic ghost coordinates are injective. -/
theorem exactGhostCoordinates_injective (k : ℕ) :
    Function.Injective (exactGhostCoordinates C k) := by
  rintro ⟨⟨x, hx⟩, ⟨⟨r, hrk⟩, hr⟩, t⟩
    ⟨⟨y, hy⟩, ⟨⟨s, hsk⟩, hs⟩, u⟩ h
  change (x, r, t.1) = (y, s, u.1) at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hxy, hrs, htu⟩
  subst y
  subst s
  have htu' : t = u := Fin.ext htu
  subst u
  rfl

/-- Positive bounded ghost slots are canonically independent of the ambient
coefficient cutoff. -/
noncomputable def boundedGhostEquivExact
    (n : ℕ) (k : Fin (n + 1)) :
    BoundedGhostSlot C n k ≃ ExactGhostSlot C k.1 where
  toFun := boundedGhostToExact C n k
  invFun := exactGhostToBounded C n k
  left_inv := by
    intro s
    apply boundedGhostCoordinates_injective C n k
    rfl
  right_inv := by
    intro s
    apply exactGhostCoordinates_injective C k.1
    rfl

/-- Every positive bounded ghost coefficient equals the intrinsic ghost
coefficient of its contribution degree. -/
theorem boundedGhostCount_eq_ghostCount
    (n : ℕ) (k : Fin (n + 1)) :
    boundedGhostCount C n k = ghostCount C k.1 := by
  exact Nat.card_congr (boundedGhostEquivExact C n k)

/-- There are no intrinsic ghost slots of contribution zero: both the copy
count and every closed-point degree are positive. -/
instance exactGhostSlotZeroIsEmpty : IsEmpty (ExactGhostSlot C 0) :=
  ⟨by
    rintro ⟨x, r, _t⟩
    have hdegree := C.atomDegree_pos x.1
    exact (Nat.not_lt_zero _) (hdegree.trans_le x.2)⟩

/-- The degree-zero intrinsic ghost coefficient vanishes. -/
@[simp]
theorem ghostCount_zero : ghostCount C 0 = 0 := by
  simp [ghostCount]

/-- The intrinsic Euler recurrence, indexed by the positive integers
`1,...,n`, follows from the marked-divisor double count and cutoff
independence. -/
theorem eulerRecurrence (n : ℕ) :
    n * C.effectiveCount n =
      ∑ j ∈ Finset.range n,
        ghostCount C (j + 1) * C.effectiveCount (n - (j + 1)) := by
  calc
    n * C.effectiveCount n =
        ∑ k : Fin (n + 1),
          ghostCount C k.1 * C.effectiveCount (n - k.1) := by
      rw [boundedEulerRecurrence]
      apply Fintype.sum_congr
      intro k
      rw [boundedGhostCount_eq_ghostCount]
    _ = ∑ j : Fin n,
          ghostCount C (j.1 + 1) *
            C.effectiveCount (n - (j.1 + 1)) := by
      rw [Fin.sum_univ_succ]
      simp
    _ = ∑ j ∈ Finset.range n,
          ghostCount C (j + 1) *
            C.effectiveCount (n - (j + 1)) := by
      simpa using
        (Fin.sum_univ_eq_sum_range
          (fun j : ℕ =>
            ghostCount C (j + 1) *
              C.effectiveCount (n - (j + 1))) n)

/-- Effective-divisor counts and intrinsic ghost counts satisfy the standard
normalized Euler recurrence.  The recurrence is now a theorem, not an input
hypothesis. -/
theorem effectiveCount_satisfiesEulerRecurrence :
    CurveZetaEulerRecurrence.SatisfiesEulerRecurrence
      C.effectiveCount (ghostCount C) := by
  exact ⟨C.effectiveCount_zero, fun n _hn => eulerRecurrence C n⟩

end ClosedPointGrading

end MazurProof.CurveZetaMarkedDivisors
