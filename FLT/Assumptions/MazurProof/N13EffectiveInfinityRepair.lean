import FLT.Assumptions.MazurProof.N13MumfordInfinityBalance

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Move the balanced upper wall by an actual Cantor principal relation. The
result lies in the effective degree-two chamber relative to two copies of
positive infinity. This does not assert an integral chart extension theorem.
-/

namespace MazurProof.N13EffectiveInfinityRepair

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

open SexticMumford N13MumfordInfinityBalance
open Polynomial

abbrev Model : SexticMumford.Model K := N13Mumford.model K

/-- If the affine degree is d, the raw order is nInf - 1. Relative to
2 infinity-plus, the two effective infinity multiplicities are nInf + 1
and 1 - d - nInf. These inequalities make both nonnegative. -/
def EffectiveChamber (E : N13Mumford.SemiMumford K) : Prop :=
  E.u.natDegree ≤ 2 ∧ -1 ≤ E.nInf ∧
    (E.u.natDegree : ℤ) + E.nInf ≤ 1

/-- The only balanced inputs outside the effective chamber are on the
upper wall d + nInf = 2. One positive-branch cubic Cantor step repairs
all of them, changing the affine polynomial and its principal relation. -/
def repair (D : N13Mumford.Mumford K) : N13Mumford.SemiMumford K :=
  if D.u.natDegree + D.nInf = 2 then plusStep D.toSemi else D.toSemi

theorem repair_class (D : N13Mumford.Mumford K) :
    semiMumfordClass Model (N13Infinity.positiveInfinityOrder K) (repair D) =
      classOf Model (N13Infinity.positiveInfinityOrder K) D := by
  unfold repair
  split
  · simpa only [semiMumfordClass_toSemi] using plusStep_class D.toSemi
  · rfl

theorem repair_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    repair D = plusStep D.toSemi := by
  simp only [repair, hwall, if_true]

theorem repair_nInf_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    (repair D).nInf = -1 := by
  rw [repair_of_upper_wall D hwall, plusStep_nInf D.toSemi D.deg_u]
  simp only [toSemi_nInf, toSemi_u]
  omega

/-- The residual horizontal polynomial is the normalized quotient
(f - V^2)/u, with V the positive-branch cubic lift. -/
theorem repair_u_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    (repair D).u = normalize (plusFactor D.toSemi) := by
  rw [repair_of_upper_wall D hwall, plusStep, cantorNextSemi_u]

/-- The residual graph uses the conjugate ordinate, including multiplicity. -/
theorem repair_v_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    (repair D).v = (-plusLift D.toSemi) % normalize (plusFactor D.toSemi) := by
  rw [repair_of_upper_wall D hwall, plusStep, cantorNextSemi_v]

/-- The actual rational function (Y - V)/normalize(w) for the repair. -/
def correction (D : N13Mumford.Mumford K) : (N13Mumford.FunctionField K)ˣ :=
  cantorCorrectionUnit Model (plusLift D.toSemi) (plusFactor D.toSemi)
    (plusFactor_ne_zero D.toSemi)

theorem correction_order (D : N13Mumford.Mumford K) :
    Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus (correction D)) =
      3 - (D.u.natDegree : ℤ) :=
  plusCorrection_order D.toSemi D.deg_u

/-- Exact affine principal-ideal relation, with the named correction
function, before passing to a quotient. -/
theorem repair_ideal_principal_relation
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    mumfordIdealUnit Model (repair D) *
        toPrincipalIdeal (CoordinateRing Model) (FunctionField Model) (correction D) =
      mumfordIdealUnit Model D.toSemi := by
  have hcongr := plusLift_congr D.toSemi
  obtain ⟨t, ht⟩ := hcongr
  have hV : plusLift D.toSemi = D.toSemi.v + D.toSemi.u * t := by
    linear_combination ht
  have hbez : ∃ a b c : K[X],
      a * D.toSemi.u + b * (2 * plusLift D.toSemi) +
        c * plusFactor D.toSemi = 1 := by
    rw [hV]
    apply cantorBezout_add_mul Model D.toSemi t (plusFactor D.toSemi)
    simpa only [N13Mumford.model_f, hV] using plusFactor_spec D.toSemi
  rw [repair_of_upper_wall D hwall]
  exact cantorConjugateSemi_principalRelation Model D.toSemi
    (plusLift D.toSemi) (plusFactor D.toSemi)
    (cantorNextNInf Model (N13Infinity.positiveInfinityOrder K) D.toSemi
      (plusLift D.toSemi) (plusFactor D.toSemi) (plusFactor_ne_zero D.toSemi))
    (plusFactor_spec D.toSemi) (plusFactor_ne_zero D.toSemi)
    (plusLift_congr D.toSemi) hbez

theorem repair_natDegree_le_two (D : N13Mumford.Mumford K) :
    (repair D).u.natDegree ≤ 2 := by
  unfold repair
  split
  · rw [plusStep_natDegree]
    exact plusFactor_natDegree_le_two D.toSemi D.deg_u
  · exact D.deg_u

theorem repair_effective (D : N13Mumford.Mumford K) :
    EffectiveChamber (repair D) := by
  refine ⟨repair_natDegree_le_two D, ?_⟩
  by_cases hwall : D.u.natDegree + D.nInf = 2
  · rw [repair_nInf_of_upper_wall D hwall]
    have hd := repair_natDegree_le_two D
    omega
  · have hb := D.infinity_bound
    simp only [repair, hwall, if_false, toSemi_nInf, toSemi_u]
    omega

/-- The degree-one/nInf=1 case changes to the residual quadratic-or-lower
graph, with raw infinity exponent -2. -/
theorem repair_degree_one
    (D : N13Mumford.Mumford K)
    (hd : D.u.natDegree = 1) (hn : D.nInf = 1) :
    repair D = plusStep D.toSemi ∧ (repair D).nInf = -1 := by
  have hwall : D.u.natDegree + D.nInf = 2 := by omega
  exact ⟨repair_of_upper_wall D hwall, repair_nInf_of_upper_wall D hwall⟩

/-- Every balanced degree-two input is on the upper wall and gets the
same concrete residual-graph repair. -/
theorem repair_degree_two
    (D : N13Mumford.Mumford K) (hd : D.u.natDegree = 2) :
    repair D = plusStep D.toSemi ∧ (repair D).nInf = -1 := by
  have hb := D.infinity_bound
  have hwall : D.u.natDegree + D.nInf = 2 := by omega
  exact ⟨repair_of_upper_wall D hwall, repair_nInf_of_upper_wall D hwall⟩

/-- Coefficients for an actual effective infinity completion of the repaired
affine graph; no natural-number truncation changes their integer values. -/
def positiveMultiplicity (E : N13Mumford.SemiMumford K) : ℕ :=
  Int.toNat (E.nInf + 1)

def negativeMultiplicity (E : N13Mumford.SemiMumford K) : ℕ :=
  Int.toNat (1 - (E.u.natDegree : ℤ) - E.nInf)

theorem positiveMultiplicity_cast
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    (positiveMultiplicity E : ℤ) = E.nInf + 1 := by
  apply Int.toNat_of_nonneg
  have := h.2.1
  omega

theorem negativeMultiplicity_cast
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    (negativeMultiplicity E : ℤ) = 1 - (E.u.natDegree : ℤ) - E.nInf := by
  apply Int.toNat_of_nonneg
  have := h.2.2
  omega

theorem completed_degree_two
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    E.u.natDegree + positiveMultiplicity E + negativeMultiplicity E = 2 := by
  have hp := positiveMultiplicity_cast E h
  have hm := negativeMultiplicity_cast E h
  omega

theorem infinity_mark_eq_positiveMultiplicity_sub_two
    (E : N13Mumford.SemiMumford K) (h : EffectiveChamber E) :
    E.nInf - 1 = (positiveMultiplicity E : ℤ) - 2 := by
  rw [positiveMultiplicity_cast E h]
  omega

theorem repaired_upper_wall_multiplicities
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    positiveMultiplicity (repair D) = 0 ∧
      negativeMultiplicity (repair D) = 2 - (repair D).u.natDegree := by
  have hn := repair_nInf_of_upper_wall D hwall
  have hh := repair_effective D
  have hp := positiveMultiplicity_cast (repair D) hh
  have hm := negativeMultiplicity_cast (repair D) hh
  have hd := hh.1
  omega

/-- The representative is given explicitly; existence is not an assumption. -/
theorem exists_effective_representative (D : N13Mumford.Mumford K) :
    ∃ E : N13Mumford.SemiMumford K, EffectiveChamber E ∧
      semiMumfordClass Model (N13Infinity.positiveInfinityOrder K) E =
        classOf Model (N13Infinity.positiveInfinityOrder K) D :=
  ⟨repair D, repair_effective D, repair_class D⟩

end
end MazurProof.N13EffectiveInfinityRepair
