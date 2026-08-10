import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoKoszul
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Degreewise shifted Koszul resolution for the N25 binary canonical cone

The natural-number parameter `debt` encodes the usual negative shift:
`shiftedPiece debt n` is the degree-`n` piece of `S(-debt)`, namely
the homogeneous polynomials of degree `n-debt`.  It is zero when `n<debt`.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoGradedKoszul

open MazurProof.RationalPointsN25QuotientTwoConormal

/-- The binary ground field. -/
abbrev k := ZMod 2

/-- The standard graded polynomial ring of the canonical affine cone. -/
abbrev S := BinaryHomogeneousRing

/-- Multiplying by a homogeneous polynomial shifts every homogeneous
component by its degree.  This is the componentwise form of graded
multiplication and avoids expanding monomial coefficients. -/
theorem homogeneousComponent_mul_left {q : S} {d : ℕ}
    (hq : q.IsHomogeneous d) (s : S) (m : ℕ) :
    MvPolynomial.homogeneousComponent (d + m) (q * s) =
      q * MvPolynomial.homogeneousComponent m s := by
  nth_rw 1 [← MvPolynomial.sum_homogeneousComponent s]
  rw [Finset.mul_sum, map_sum]
  simp_rw [MvPolynomial.homogeneousComponent_of_mem
    (hq.mul (MvPolynomial.homogeneousComponent_isHomogeneous _ _))]
  by_cases hm : m ∈ Finset.range (s.totalDegree + 1)
  · simp [hm, Nat.add_left_cancel_iff]
  · have hdegree : s.totalDegree < m := by
      simpa [Finset.mem_range, Nat.lt_succ_iff] using hm
    rw [MvPolynomial.homogeneousComponent_eq_zero _ _ hdegree]
    simp [hm, Nat.add_left_cancel_iff]

/-- If every homogeneous component except degree `t` vanishes, then the
polynomial equals its degree-`t` component. -/
theorem eq_homogeneousComponent_of_other_eq_zero (s : S) (t : ℕ)
    (hzero : ∀ m, m ≠ t → MvPolynomial.homogeneousComponent m s = 0) :
    s = MvPolynomial.homogeneousComponent t s := by
  calc
    s = ∑ i ∈ Finset.range (s.totalDegree + 1),
        MvPolynomial.homogeneousComponent i s :=
      (MvPolynomial.sum_homogeneousComponent s).symm
    _ = ∑ i ∈ Finset.range (s.totalDegree + 1),
        if i = t then MvPolynomial.homogeneousComponent t s else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hit : i = t
            · subst i
              simp
            · simp [hit, hzero i hit]
    _ = MvPolynomial.homogeneousComponent t s := by
      by_cases ht : t ∈ Finset.range (s.totalDegree + 1)
      · simp [ht]
      · have hdegree : s.totalDegree < t := by
          simpa [Finset.mem_range, Nat.lt_succ_iff] using ht
        rw [MvPolynomial.homogeneousComponent_eq_zero _ _ hdegree]
        simp

/-- Cancellation by a nonzero homogeneous factor preserves homogeneity and
subtracts its degree.  The proof compares homogeneous components, using the
domain property only to cancel the fixed factor. -/
theorem isHomogeneous_of_mul_left {q s : S} {d N : ℕ}
    (hq0 : q ≠ 0) (hq : q.IsHomogeneous d)
    (hqs : (q * s).IsHomogeneous N) :
    s.IsHomogeneous (N - d) := by
  have hcomponent (m : ℕ) (hm : d + m ≠ N) :
      MvPolynomial.homogeneousComponent m s = 0 := by
    have hzero : MvPolynomial.homogeneousComponent (d + m) (q * s) = 0 := by
      rw [MvPolynomial.homogeneousComponent_of_mem hqs]
      simp [hm]
    rw [homogeneousComponent_mul_left hq s m] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hq0
  by_cases hdN : d ≤ N
  · have hother (m : ℕ) (hm : m ≠ N - d) :
        MvPolynomial.homogeneousComponent m s = 0 :=
      hcomponent m (by omega)
    rw [eq_homogeneousComponent_of_other_eq_zero s (N - d) hother]
    exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
  · have hall (m : ℕ) : MvPolynomial.homogeneousComponent m s = 0 :=
      hcomponent m (by omega)
    have hs0 : s = 0 := by
      rw [← MvPolynomial.sum_homogeneousComponent s]
      simp_rw [hall]
      simp
    rw [hs0]
    exact MvPolynomial.isHomogeneous_zero (Fin 4) k (N - d)

/-- A nonzero degree-`d` homogeneous factor cannot multiply a nonzero
polynomial to a homogeneous element of smaller degree. -/
theorem eq_zero_of_mul_left_homogeneous_of_lt {q s : S} {d N : ℕ}
    (hq0 : q ≠ 0) (hq : q.IsHomogeneous d)
    (hqs : (q * s).IsHomogeneous N) (hN : N < d) :
    s = 0 := by
  have hs := isHomogeneous_of_mul_left hq0 hq hqs
  by_contra hs0
  have hprod0 : q * s ≠ 0 := mul_ne_zero hq0 hs0
  have hdegree := (hq.mul hs).inj_right hqs hprod0
  omega

/-- The degree-`n` piece of the negatively shifted free module `S(-debt)`.
The piece is zero below the shift. -/
def shiftedPiece (debt n : ℕ) : Submodule k S :=
  if debt ≤ n then MvPolynomial.homogeneousSubmodule (Fin 4) k (n - debt)
  else ⊥

/-- Every element of `S(-debt)_n` is homogeneous of degree `n-debt`; below
the shift the only element is zero, which is homogeneous in every degree. -/
theorem shiftedPiece_isHomogeneous {debt n : ℕ}
    (r : shiftedPiece debt n) :
    (r : S).IsHomogeneous (n - debt) := by
  by_cases hdegree : debt ≤ n
  · simpa [shiftedPiece, hdegree] using r.property
  · have hr0 : (r : S) = 0 := by
      simpa [shiftedPiece, hdegree] using r.property
    rw [hr0]
    exact MvPolynomial.isHomogeneous_zero (Fin 4) k (n - debt)

/-- Left multiplication by a polynomial, regarded as a linear map over the
binary ground field. -/
def mulLinear (p : S) : S →ₗ[k] S :=
  (LinearMap.lsmul S S p).restrictScalars k

/-- Multiplication by a degree-`d` homogeneous polynomial maps the degree-`n`
piece of `S(-(e+d))` into the degree-`n` piece of `S(-e)`. -/
def homogeneousMul (p : S) (d e n : ℕ) (hp : p.IsHomogeneous d) :
    shiftedPiece (e + d) n →ₗ[k] shiftedPiece e n :=
  ((mulLinear p).domRestrict (shiftedPiece (e + d) n)).codRestrict
    (shiftedPiece e n) (fun x ↦ by
      by_cases hsource : e + d ≤ n
      · have htarget : e ≤ n := by omega
        have hx : (x : S).IsHomogeneous (n - (e + d)) := by
          simpa [shiftedPiece, hsource] using x.property
        have hprod := hp.mul hx
        have hdegree : d + (n - (e + d)) = n - e := by omega
        rw [shiftedPiece, if_pos htarget]
        change (p * (x : S)).IsHomogeneous (n - e)
        simpa only [hdegree] using hprod
      · have hx : (x : S) = 0 := by
          simpa [shiftedPiece, hsource] using x.property
        simp [hx])

/-- Forgetting the degree witness, `homogeneousMul` is ordinary left
multiplication. -/
@[simp]
theorem homogeneousMul_coe (p : S) (d e n : ℕ) (hp : p.IsHomogeneous d)
    (r : shiftedPiece (e + d) n) :
    ((homogeneousMul p d e n hp r : shiftedPiece e n) : S) = p * (r : S) :=
  rfl

/-- The degree-`n` first Koszul differential
`S(-5) → S(-2) ⊕ S(-3)`. -/
def gradedKoszulTop (n : ℕ) :
    shiftedPiece 5 n →ₗ[k] shiftedPiece 2 n × shiftedPiece 3 n :=
  (homogeneousMul canonicalCubicPolynomial25Two 3 2 n
      canonicalCubicPolynomial25Two_isHomogeneous).prod
    (-(homogeneousMul canonicalQuadricPolynomial25Two 2 3 n
      canonicalQuadricPolynomial25Two_isHomogeneous))

/-- The degree-`n` second Koszul differential
`S(-2) ⊕ S(-3) → S`. -/
def gradedKoszulMiddle (n : ℕ) :
    shiftedPiece 2 n × shiftedPiece 3 n →ₗ[k] shiftedPiece 0 n :=
  (homogeneousMul canonicalQuadricPolynomial25Two 2 0 n
      canonicalQuadricPolynomial25Two_isHomogeneous).coprod
    (homogeneousMul canonicalCubicPolynomial25Two 3 0 n
      canonicalCubicPolynomial25Two_isHomogeneous)

/-- After forgetting degrees, the first component of the shifted top map is
multiplication by the cubic. -/
@[simp]
theorem gradedKoszulTop_fst_coe (n : ℕ) (r : shiftedPiece 5 n) :
    (((gradedKoszulTop n r).1 : shiftedPiece 2 n) : S) =
      canonicalCubicPolynomial25Two * (r : S) :=
  rfl

/-- After forgetting degrees, the second component of the shifted top map is
minus multiplication by the quadric. -/
@[simp]
theorem gradedKoszulTop_snd_coe (n : ℕ) (r : shiftedPiece 5 n) :
    (((gradedKoszulTop n r).2 : shiftedPiece 3 n) : S) =
      -(canonicalQuadricPolynomial25Two * (r : S)) :=
  rfl

/-- After forgetting degrees, the shifted middle map is the ordinary
quadric-cubic linear combination. -/
@[simp]
theorem gradedKoszulMiddle_coe (n : ℕ)
    (p : shiftedPiece 2 n × shiftedPiece 3 n) :
    ((gradedKoszulMiddle n p : shiftedPiece 0 n) : S) =
      canonicalQuadricPolynomial25Two * (p.1 : S) +
        canonicalCubicPolynomial25Two * (p.2 : S) :=
  rfl

/-- The degreewise first Koszul differential is injective.  This is the
graded restriction of the already proved ambient injectivity. -/
theorem gradedKoszulTop_injective (n : ℕ) :
    Function.Injective (gradedKoszulTop n) := by
  intro a b hab
  apply Subtype.ext
  apply RationalPointsN25QuotientTwoKoszul.koszulTop_injective
  apply Prod.ext
  · simpa only [RationalPointsN25QuotientTwoKoszul.koszulTop_apply,
      gradedKoszulTop_fst_coe] using
      congrArg (fun p ↦ ((p.1 : shiftedPiece 2 n) : S)) hab
  · simpa only [RationalPointsN25QuotientTwoKoszul.koszulTop_apply,
      gradedKoszulTop_snd_coe] using
      congrArg (fun p ↦ ((p.2 : shiftedPiece 3 n) : S)) hab

/-- Exactness in every total degree: an ungraded Koszul witness is forced to
have degree `n-5` by cancellation of the nonzero homogeneous quadric. -/
theorem gradedKoszul_exact_top_middle (n : ℕ) :
    Function.Exact (gradedKoszulTop n) (gradedKoszulMiddle n) := by
  intro p
  constructor
  · intro hp
    have hpCoe := congrArg (fun r ↦ ((r : shiftedPiece 0 n) : S)) hp
    have hpGlobal :
        RationalPointsN25QuotientTwoKoszul.koszulMiddle
          ((p.1 : S), (p.2 : S)) = 0 := by
      simpa only [RationalPointsN25QuotientTwoKoszul.koszulMiddle_apply,
        gradedKoszulMiddle_coe, LinearMap.zero_apply, Submodule.coe_zero] using hpCoe
    rcases
        (RationalPointsN25QuotientTwoKoszul.koszul_exact_top_middle
          ((p.1 : S), (p.2 : S))).mp hpGlobal with
      ⟨r, hr⟩
    have hsecond :
        -(canonicalQuadricPolynomial25Two * r) = (p.2 : S) := by
      simpa only [RationalPointsN25QuotientTwoKoszul.koszulTop_apply] using
        congrArg Prod.snd hr
    have hquadricMul :
        (canonicalQuadricPolynomial25Two * r).IsHomogeneous (n - 3) := by
      have hneg : canonicalQuadricPolynomial25Two * r = -(p.2 : S) := by
        linear_combination -hsecond
      rw [hneg]
      exact (shiftedPiece_isHomogeneous p.2).neg
    have hrHomogeneous : r.IsHomogeneous ((n - 3) - 2) :=
      isHomogeneous_of_mul_left
        RationalPointsN25QuotientTwoRegularSequence.canonicalQuadricPolynomial25Two_ne_zero
        canonicalQuadricPolynomial25Two_isHomogeneous hquadricMul
    have hrMem : r ∈ shiftedPiece 5 n := by
      by_cases hfive : 5 ≤ n
      · rw [shiftedPiece, if_pos hfive]
        have hdegree : (n - 3) - 2 = n - 5 := by omega
        simpa only [MvPolynomial.mem_homogeneousSubmodule, hdegree] using
          hrHomogeneous
      · have hsmall : n - 3 < 2 := by omega
        have hr0 := eq_zero_of_mul_left_homogeneous_of_lt
          RationalPointsN25QuotientTwoRegularSequence.canonicalQuadricPolynomial25Two_ne_zero
          canonicalQuadricPolynomial25Two_isHomogeneous hquadricMul hsmall
        simp [shiftedPiece, hfive, hr0]
    let rGraded : shiftedPiece 5 n := ⟨r, hrMem⟩
    refine ⟨rGraded, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simpa only [gradedKoszulTop_fst_coe,
        RationalPointsN25QuotientTwoKoszul.koszulTop_apply] using
        congrArg Prod.fst hr
    · apply Subtype.ext
      simpa only [gradedKoszulTop_snd_coe,
        RationalPointsN25QuotientTwoKoszul.koszulTop_apply] using
        congrArg Prod.snd hr
  · rintro ⟨r, rfl⟩
    apply Subtype.ext
    simp [gradedKoszulMiddle, gradedKoszulTop, homogeneousMul, mulLinear]
    ring

/-- The two shifted degreewise Koszul differentials compose to zero. -/
theorem gradedKoszulMiddle_comp_top (n : ℕ) :
    (gradedKoszulMiddle n).comp (gradedKoszulTop n) = 0 := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  simp [gradedKoszulMiddle, gradedKoszulTop, homogeneousMul, mulLinear]
  ring

/-- The degree-`n` coordinate-ring piece, presented as the cokernel of the
degreewise quadric-cubic relation map. -/
abbrev canonicalConePiece (n : ℕ) :=
  shiftedPiece 0 n ⧸ LinearMap.range (gradedKoszulMiddle n)

/-- The degreewise projection onto the presented coordinate-ring piece. -/
def gradedConeProjection (n : ℕ) :
    shiftedPiece 0 n →ₗ[k] canonicalConePiece n :=
  Submodule.mkQ (LinearMap.range (gradedKoszulMiddle n))

/-- Exactness at `S_n` is the defining cokernel property of the degreewise
coordinate-ring presentation. -/
theorem gradedKoszul_exact_middle_projection (n : ℕ) :
    Function.Exact (gradedKoszulMiddle n) (gradedConeProjection n) := by
  rw [LinearMap.exact_iff]
  exact Submodule.ker_mkQ (LinearMap.range (gradedKoszulMiddle n))

/-- The degreewise quotient projection is surjective. -/
theorem gradedConeProjection_surjective (n : ℕ) :
    Function.Surjective (gradedConeProjection n) :=
  Submodule.mkQ_surjective (LinearMap.range (gradedKoszulMiddle n))

end MazurProof.RationalPointsN25QuotientTwoGradedKoszul
