import FLT.Assumptions.MazurProof.N13ReductionClassifier

/-!
# Relation-first specialization from integral spreads

An integral spread has a generic class and a special class.  Specialization
is first expressed as the relation saying that one spread realizes both
classes.  Existence of spreads and the assertion that generic equality is
equivalent to special equality make every relational fibre a singleton.
Only then do we choose a classifier.
-/

namespace MazurProof.N13SpreadClassifier

noncomputable section

universe u v w

variable {G : Type u} {S : Type v} {Line : Type w}
variable [AddCommGroup G]

/-- The exact geometric interface for relation-first specialization. -/
structure SpreadData
    (G : Type u) (S : Type v) (Line : Type w)
    [AddCommGroup G] where
  kernel : AddSubgroup G
  genericClass : Line → G ⧸ kernel
  specialClass : Line → S
  exists_spread :
    ∀ P : G, ∃ L : Line,
      genericClass L = QuotientAddGroup.mk' kernel P
  class_eq_iff :
    ∀ L M : Line,
      specialClass L = specialClass M ↔
        genericClass L = genericClass M

namespace SpreadData

variable (D : SpreadData G S Line)

/-- A rational class reduces to a special class if one integral spread
realizes both. -/
def ReducesTo (P : G) (s : S) : Prop :=
  ∃ L : Line,
    D.genericClass L = QuotientAddGroup.mk' D.kernel P ∧
      D.specialClass L = s

theorem reducesTo_exists (P : G) :
    ∃ s : S, D.ReducesTo P s := by
  obtain ⟨L, hL⟩ := D.exists_spread P
  exact ⟨D.specialClass L, L, hL, rfl⟩

theorem reducesTo_unique
    (P : G) {s t : S}
    (hs : D.ReducesTo P s)
    (ht : D.ReducesTo P t) :
    s = t := by
  obtain ⟨L, hL, rfl⟩ := hs
  obtain ⟨M, hM, rfl⟩ := ht
  apply (D.class_eq_iff L M).2
  exact hL.trans hM.symm

/-- A chosen spread, introduced only after relational existence and
uniqueness have been established. -/
def spread (P : G) : Line :=
  Classical.choose (D.exists_spread P)

@[simp] theorem genericClass_spread (P : G) :
    D.genericClass (D.spread P) =
      QuotientAddGroup.mk' D.kernel P :=
  Classical.choose_spec (D.exists_spread P)

/-- The unique special class realized by an integral spread. -/
def classify (P : G) : S :=
  D.specialClass (D.spread P)

theorem reducesTo_classify (P : G) :
    D.ReducesTo P (D.classify P) :=
  ⟨D.spread P, D.genericClass_spread P, rfl⟩

theorem reducesTo_iff_eq_classify
    (P : G) (s : S) :
    D.ReducesTo P s ↔ s = D.classify P := by
  constructor
  · intro hs
    exact D.reducesTo_unique P hs (D.reducesTo_classify P)
  · rintro rfl
    exact D.reducesTo_classify P

/-- Equality of chosen specializations is exactly equality modulo the
geometric kernel. -/
theorem classify_eq_iff
    (P Q : G) :
    D.classify P = D.classify Q ↔ P - Q ∈ D.kernel := by
  change
    D.specialClass (D.spread P) =
        D.specialClass (D.spread Q) ↔
      P - Q ∈ D.kernel
  rw [D.class_eq_iff,
    D.genericClass_spread, D.genericClass_spread]
  change
    (↑P : G ⧸ D.kernel) = (↑Q : G ⧸ D.kernel) ↔
      P - Q ∈ D.kernel
  exact QuotientAddGroup.eq_iff_sub_mem

/-- Package relation-first specialization as the exact set-valued
classifier consumed by the rational-point endgame. -/
def classifierData :
    N13ReductionClassifier.Data G S where
  kernel := D.kernel
  classify := D.classify
  exact := D.classify_eq_iff

end SpreadData

end

end MazurProof.N13SpreadClassifier
