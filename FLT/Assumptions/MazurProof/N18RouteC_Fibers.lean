import FLT.Assumptions.MazurProof.N18RouteC_Finiteness

/-!
# Finite degree-two fiber tables for N18 Route C

Once `E₀(L) ≃ ZMod 21` and a complete projective degree-two quotient table
are supplied, every curve point injects into one of `21 × 2 = 42` slots.  A
second optional-value table performs the rationality filter.
-/

namespace MazurProof.N18RouteC.Fibers

noncomputable section

abbrev Z21 := ZMod 21
abbrev FiberSlot := Z21 × Fin 2

theorem natCard_fiberSlot : Nat.card FiberSlot = 42 := by
  simp [FiberSlot, Nat.card_zmod]

structure DegreeTwoFiberTable
    (CQ CL E : Type*) [AddCommGroup E] where
  baseChange : CQ ↪ CL
  qPlus : CL → E
  enumE : Z21 ≃+ E
  pointAt : FiberSlot → Option CL
  pointAt_sound :
    ∀ s : FiberSlot, ∀ P : CL,
      pointAt s = some P → qPlus P = enumE s.1
  pointAt_complete :
    ∀ P : CL, ∃ i : Fin 2,
      pointAt (enumE.symm (qPlus P), i) = some P

namespace DegreeTwoFiberTable

variable {CQ CL E : Type*} [AddCommGroup E]
    (T : DegreeTwoFiberTable CQ CL E)

def GeometricCandidate :=
  {P : CL // ∃ s : FiberSlot, T.pointAt s = some P}

def chosenSlot (P : T.GeometricCandidate) : FiberSlot :=
  Classical.choose P.property

theorem chosenSlot_spec (P : T.GeometricCandidate) :
    T.pointAt (T.chosenSlot P) = some P.val :=
  Classical.choose_spec P.property

theorem chosenSlot_injective :
    Function.Injective T.chosenSlot := by
  intro P Q h
  apply Subtype.ext
  have hP := T.chosenSlot_spec P
  have hQ := T.chosenSlot_spec Q
  rw [h] at hP
  exact Option.some.inj (hP.symm.trans hQ)

def pointToCandidate (P : CL) : T.GeometricCandidate :=
  ⟨P, by
    obtain ⟨i, hi⟩ := T.pointAt_complete P
    exact ⟨(T.enumE.symm (T.qPlus P), i), hi⟩⟩

def pointSlot (P : CL) : FiberSlot :=
  T.chosenSlot (T.pointToCandidate P)

theorem pointSlot_injective :
    Function.Injective (pointSlot T) := by
  intro P Q h
  have hc : T.pointToCandidate P = T.pointToCandidate Q :=
    T.chosenSlot_injective h
  exact congrArg Subtype.val hc

include T in
theorem curvePoints_finite : Finite CL :=
  Finite.of_injective (pointSlot T) (pointSlot_injective T)

include T in
theorem curvePoints_card_le_42 : Nat.card CL ≤ 42 := by
  letI : Finite CL := curvePoints_finite T
  calc
    Nat.card CL ≤ Nat.card FiberSlot :=
      Finiteness.natCard_le_of_injective (pointSlot T) (pointSlot_injective T)
    _ = 42 := natCard_fiberSlot

def rationalPointSlot (P : CQ) : FiberSlot :=
  pointSlot T (T.baseChange P)

theorem rationalPointSlot_injective :
    Function.Injective (rationalPointSlot T) := by
  intro P Q h
  apply T.baseChange.injective
  exact pointSlot_injective T h

def C_Q_points (_ : DegreeTwoFiberTable CQ CL E) : Set CQ := Set.univ

theorem C_Q_points_finite : T.C_Q_points.Finite := by
  letI : Finite CQ :=
    Finite.of_injective (rationalPointSlot T) (rationalPointSlot_injective T)
  simpa [C_Q_points] using
    (Set.finite_univ : (Set.univ : Set CQ).Finite)

include T in
theorem rationalPoints_card_le_42 : Nat.card CQ ≤ 42 := by
  letI : Finite CQ :=
    Finite.of_injective (rationalPointSlot T) (rationalPointSlot_injective T)
  calc
    Nat.card CQ ≤ Nat.card FiberSlot :=
      Finiteness.natCard_le_of_injective (rationalPointSlot T)
        (rationalPointSlot_injective T)
    _ = 42 := natCard_fiberSlot

end DegreeTwoFiberTable

structure RationalFiberCertificate
    (CQ CL E : Type*) [AddCommGroup E] where
  geom : DegreeTwoFiberTable CQ CL E
  rationalAt : FiberSlot → Option CQ
  rationalAt_sound :
    ∀ s : FiberSlot, ∀ P : CQ,
      rationalAt s = some P →
        geom.pointAt s = some (geom.baseChange P)
  rationalAt_complete :
    ∀ P : CQ, ∃ s : FiberSlot, rationalAt s = some P

namespace RationalFiberCertificate

variable {CQ CL E : Type*} [AddCommGroup E]
    [DecidableEq CQ]
    (R : RationalFiberCertificate CQ CL E)

def rationalCandidateFinset : Finset CQ :=
  Finset.univ.biUnion fun s : FiberSlot ↦
    (R.rationalAt s).toFinset

theorem rational_mem_candidateFinset (P : CQ) :
    P ∈ R.rationalCandidateFinset := by
  obtain ⟨s, hs⟩ := R.rationalAt_complete P
  rw [rationalCandidateFinset, Finset.mem_biUnion]
  exact ⟨s, Finset.mem_univ s, by simp [hs]⟩

theorem rationalCandidateFinset_card_le_42 :
    R.rationalCandidateFinset.card ≤ 42 := by
  letI : Finite CQ :=
    Finite.of_injective (DegreeTwoFiberTable.rationalPointSlot R.geom)
      (DegreeTwoFiberTable.rationalPointSlot_injective R.geom)
  letI : Fintype CQ := Fintype.ofFinite CQ
  calc
    R.rationalCandidateFinset.card ≤ Fintype.card CQ := by
      simpa using
        Finset.card_le_card
          (Finset.subset_univ R.rationalCandidateFinset)
    _ = Nat.card CQ := by simp
    _ ≤ 42 := DegreeTwoFiberTable.rationalPoints_card_le_42 R.geom

theorem all_rational_points_mem
    (cusps : Finset CQ)
    (hcheck : R.rationalCandidateFinset = cusps) :
    ∀ P : CQ, P ∈ cusps := by
  intro P
  rw [← hcheck]
  exact R.rational_mem_candidateFinset P

end RationalFiberCertificate

end

end MazurProof.N18RouteC.Fibers
