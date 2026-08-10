import FLT.Assumptions.MazurProof.CurveZetaClassNumber
import FLT.Assumptions.MazurProof.CurveDivisorPicard

/-!
# The middle-degree Riemann--Roch class-number identity

For a genus-`g` curve over `F_q`, Riemann--Roch in degree `g` pairs a
degree-`g` Picard class `c` with the residual degree-`g-2` class `K-c` and
gives

`l(c) = 1 + l(K-c)`.

A complete linear system with `r` sections has `1+q+...+q^(r-1)` effective
divisors.  Summing the resulting identity

`#|c| = 1 + q * #|K-c|`

over Picard classes proves

`A_g = q A_(g-2) + #Pic^0`.

This file proves the finite-cardinality argument.  The honest geometric seam
is exposed as the residual equivalence, the two complete-linear-system fibre
formulas, the Riemann--Roch rank identity, and the translation from `Pic^g`
to `Pic^0`.
-/

namespace MazurProof.CurveZetaMiddleRiemannRoch

open CurveZetaClassNumber
open scoped BigOperators

/-! ## Finite fibre partitions -/

/-- A finite type is the disjoint union of the fibres of any map to another
finite type.  This is the counting form used for the two Picard degrees. -/
theorem card_eq_sum_fiber_card
    {Source Target : Type*} [Finite Source] [Fintype Target]
    (f : Source → Target) :
    Nat.card Source = ∑ c : Target, Nat.card {x : Source // f x = c} := by
  classical
  letI := Fintype.ofFinite Source
  calc
    Nat.card Source = Nat.card (Σ c, {x : Source // f x = c}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ c : Target, Nat.card {x : Source // f x = c} := Nat.card_sigma

/-! ## Complete linear systems -/

/-- Adding one section to a complete linear system adds one fixed point and
`q` copies of the previous projective space.  In geometric-sum notation this
is `#P^r(F_q) = 1 + q * #P^(r-1)(F_q)`. -/
theorem linearSystemCard_succ (q r : ℕ) :
    linearSystemCard q (r + 1) = 1 + q * linearSystemCard q r := by
  simp only [linearSystemCard, geom_sum_succ]
  omega

/-! ## Summed middle-degree Riemann--Roch -/

/-- The finite counting theorem behind `A_g = q A_(g-2) + #Pic^0`.

`residual` models `c ↦ K-c`.  The ranks are dimensions of the corresponding
Riemann--Roch spaces.  Thus `hRR` is precisely the degree-`g` Riemann--Roch
identity, while `hHighFiber` and `hLowFiber` identify effective divisors in a
class with its complete linear system. -/
theorem effective_card_middle_degree
    {PicHigh PicLow EffectiveHigh EffectiveLow : Type*}
    [Fintype PicHigh] [Finite EffectiveHigh] [Finite EffectiveLow]
    (classHigh : EffectiveHigh → PicHigh)
    (classLow : EffectiveLow → PicLow)
    (residual : PicHigh ≃ PicLow)
    (rankHigh : PicHigh → ℕ) (rankLow : PicLow → ℕ)
    (q : ℕ)
    (hHighFiber : ∀ c,
      Nat.card {D : EffectiveHigh // classHigh D = c} =
        linearSystemCard q (rankHigh c))
    (hLowFiber : ∀ c,
      Nat.card {D : EffectiveLow // classLow D = c} =
        linearSystemCard q (rankLow c))
    (hRR : ∀ c, rankHigh c = rankLow (residual c) + 1) :
    Nat.card EffectiveHigh =
      Fintype.card PicHigh + q * Nat.card EffectiveLow := by
  classical
  letI := Fintype.ofEquiv PicHigh residual
  rw [card_eq_sum_fiber_card classHigh]
  simp_rw [hHighFiber, hRR, linearSystemCard_succ]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.mul_one]
  rw [← Finset.mul_sum]
  have hResidualSum :
      (∑ c : PicHigh, linearSystemCard q (rankLow (residual c))) =
        ∑ c : PicLow, linearSystemCard q (rankLow c) :=
    residual.sum_comp (fun c => linearSystemCard q (rankLow c))
  rw [hResidualSum]
  rw [card_eq_sum_fiber_card classLow]
  simp_rw [hLowFiber]
  simp only [Nat.cast_id]

/-- Translating degree-`g` Picard classes to degree zero turns the middle
Riemann--Roch count into the usual class-number identity.  For N25 the inputs
are `g=4`, `q=3`, `EffectiveHigh=DivEff^4`, and
`EffectiveLow=DivEff^2`. -/
theorem effective_card_middle_degree_picardZero
    {PicZero PicHigh PicLow EffectiveHigh EffectiveLow : Type*}
    [Fintype PicZero] [Fintype PicHigh]
    [Fintype EffectiveHigh] [Fintype EffectiveLow]
    (classHigh : EffectiveHigh → PicHigh)
    (classLow : EffectiveLow → PicLow)
    (residual : PicHigh ≃ PicLow)
    (rankHigh : PicHigh → ℕ) (rankLow : PicLow → ℕ)
    (q : ℕ)
    (hHighFiber : ∀ c,
      Nat.card {D : EffectiveHigh // classHigh D = c} =
        linearSystemCard q (rankHigh c))
    (hLowFiber : ∀ c,
      Nat.card {D : EffectiveLow // classLow D = c} =
        linearSystemCard q (rankLow c))
    (hRR : ∀ c, rankHigh c = rankLow (residual c) + 1)
    (hPicard : Fintype.card PicHigh = Fintype.card PicZero) :
    Fintype.card EffectiveHigh =
      q * Fintype.card EffectiveLow + Fintype.card PicZero := by
  have h := effective_card_middle_degree classHigh classLow residual rankHigh rankLow
    q hHighFiber hLowFiber hRR
  rw [hPicard] at h
  simpa only [Nat.card_eq_fintype_card, add_comm] using h

/-! ## The genus-four identity on the actual divisor-class quotient -/

/-- The middle-degree count specialized to the divisor class group built from
closed points and a degree-zero principal-divisor subgroup.

Unlike `effective_card_middle_degree_picardZero`, this theorem does not allow
unrelated finite types to stand in for `Pic^0`, `Pic^2`, and `Pic^4`.  All
three are fibres of the descended degree map on one quotient group.  A
degree-one base class supplies `Pic^4 ≃ Pic^0`, while a degree-six canonical
class supplies the residual equivalence `Pic^4 ≃ Pic^2`.  The remaining fibre
and rank hypotheses are exactly the geometric complete-linear-system and
Riemann--Roch statements. -/
theorem effective_card_genus_four_divisorPicard
    (C : CurveZetaEffectiveDivisors.ClosedPointGrading)
    (Principal : AddSubgroup C.Divisor)
    (hPrincipal : Principal ≤ C.divisorDegree.ker)
    (base canonical : C.DivisorClass Principal)
    (hbase : C.classDegree Principal hPrincipal base = 1)
    (hcanonical : C.classDegree Principal hPrincipal canonical = 6)
    [Fintype (C.PicDegree Principal hPrincipal 0)]
    (rankFour : C.PicDegree Principal hPrincipal 4 → ℕ)
    (rankTwo : C.PicDegree Principal hPrincipal 2 → ℕ)
    (q : ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : C.EffDivOfDegree 4 //
        C.effectiveClass Principal hPrincipal 4 D = c} =
          linearSystemCard q (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : C.EffDivOfDegree 2 //
        C.effectiveClass Principal hPrincipal 2 D = c} =
          linearSystemCard q (rankTwo c))
    (hRR : ∀ c,
      rankFour c =
        rankTwo (C.residualDegreeFourTwo Principal hPrincipal canonical
          hcanonical c) + 1) :
    Nat.card (C.EffDivOfDegree 4) =
      q * Nat.card (C.EffDivOfDegree 2) +
        Fintype.card (C.PicDegree Principal hPrincipal 0) := by
  classical
  letI : Fintype (C.EffDivOfDegree 4) := Fintype.ofFinite _
  letI : Fintype (C.EffDivOfDegree 2) := Fintype.ofFinite _
  letI : Fintype (C.PicDegree Principal hPrincipal 4) :=
    Fintype.ofEquiv (C.PicDegree Principal hPrincipal 0)
      (C.picDegreeEquivZero Principal hPrincipal base hbase 4).symm
  have hMiddle := effective_card_middle_degree_picardZero
    (PicZero := C.PicDegree Principal hPrincipal 0)
    (C.effectiveClass Principal hPrincipal 4)
    (C.effectiveClass Principal hPrincipal 2)
    (C.residualDegreeFourTwo Principal hPrincipal canonical hcanonical)
    rankFour rankTwo q hFourFiber hTwoFiber hRR
    (Fintype.card_congr
      (C.picDegreeEquivZero Principal hPrincipal base hbase 4))
  simpa only [Nat.card_eq_fintype_card] using hMiddle

end MazurProof.CurveZetaMiddleRiemannRoch
