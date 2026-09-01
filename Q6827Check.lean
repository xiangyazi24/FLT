import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Ideal.Over
import Mathlib.Tactic.FinCases

open scoped BigOperators

namespace Q6827Check

private def fin3Enum {α : Type*} (x0 x1 x2 : α) : Fin 3 → α :=
  Fin.cases x0 (Fin.cases x1 (fun _ => x2))

private theorem fin3Enum_bijective {α : Type*}
    (x0 x1 x2 : α)
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2)
    (hcover : ∀ x : α, x = x0 ∨ x = x1 ∨ x = x2) :
    Function.Bijective (fin3Enum x0 x1 x2) := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [fin3Enum]
  · intro x
    rcases hcover x with h | h | h
    · exact ⟨0, by simpa [fin3Enum] using h.symm⟩
    · exact ⟨1, by simpa [fin3Enum] using h.symm⟩
    · exact ⟨2, by simpa [fin3Enum] using h.symm⟩

noncomputable def equivFin3OfThree {α : Type*}
    (x0 x1 x2 : α)
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2)
    (hcover : ∀ x : α, x = x0 ∨ x = x1 ∨ x = x2) :
    α ≃ Fin 3 :=
  (Equiv.ofBijective (fin3Enum x0 x1 x2)
    (fin3Enum_bijective x0 x1 x2 h01 h02 h12 hcover)).symm

section PrimesOver

variable {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
variable (p : Ideal A) (PX PY PZ : Ideal B)
variable [PX.IsPrime] [PY.IsPrime] [PZ.IsPrime]
variable [PX.LiesOver p] [PY.LiesOver p] [PZ.LiesOver p]

noncomputable def primesOverEquivFin3
    (hXY : PX ≠ PY) (hXZ : PX ≠ PZ) (hYZ : PY ≠ PZ)
    (hclass : ∀ Q : p.primesOver B,
      Q.1 = PX ∨ Q.1 = PY ∨ Q.1 = PZ) :
    p.primesOver B ≃ Fin 3 := by
  let qX : p.primesOver B := Ideal.primesOver.mk PX
  let qY : p.primesOver B := Ideal.primesOver.mk PY
  let qZ : p.primesOver B := Ideal.primesOver.mk PZ
  have hqXY : qX ≠ qY := by
    intro h
    exact hXY (by
      simpa [qX, qY] using
        congrArg (fun Q : p.primesOver B => Q.1) h)
  have hqXZ : qX ≠ qZ := by
    intro h
    exact hXZ (by
      simpa [qX, qZ] using
        congrArg (fun Q : p.primesOver B => Q.1) h)
  have hqYZ : qY ≠ qZ := by
    intro h
    exact hYZ (by
      simpa [qY, qZ] using
        congrArg (fun Q : p.primesOver B => Q.1) h)
  have hcover : ∀ Q : p.primesOver B,
      Q = qX ∨ Q = qY ∨ Q = qZ := by
    intro Q
    rcases hclass Q with h | h | h
    · left
      apply Subtype.ext
      simpa [qX] using h
    · right; left
      apply Subtype.ext
      simpa [qY] using h
    · right; right
      apply Subtype.ext
      simpa [qZ] using h
  exact equivFin3OfThree qX qY qZ hqXY hqXZ hqYZ hcover

noncomputable def primesOverEquivFin3_of_mem
    (u : A) (hu : u ∈ p)
    (hXY : PX ≠ PY) (hXZ : PX ≠ PZ) (hYZ : PY ≠ PZ)
    (hclassify : ∀ Q : Ideal B, Q.IsPrime →
      algebraMap A B u ∈ Q →
        Q = PX ∨ Q = PY ∨ Q = PZ) :
    p.primesOver B ≃ Fin 3 :=
  primesOverEquivFin3 p PX PY PZ hXY hXZ hYZ fun Q => by
    have hmem : algebraMap A B u ∈ Q.1 :=
      (Ideal.mem_of_liesOver Q.1 p u).mp hu
    exact hclassify Q.1 Q.2.1 hmem

theorem sum_primesOver_eq_three
    [Fintype (p.primesOver B)]
    {M : Type*} [AddCommMonoid M]
    (hXY : PX ≠ PY) (hXZ : PX ≠ PZ) (hYZ : PY ≠ PZ)
    (hclass : ∀ Q : p.primesOver B,
      Q.1 = PX ∨ Q.1 = PY ∨ Q.1 = PZ)
    (f : p.primesOver B → M) :
    (∑ Q : p.primesOver B, f Q) =
      f (Ideal.primesOver.mk PX) +
        f (Ideal.primesOver.mk PY) +
        f (Ideal.primesOver.mk PZ) := by
  let qX : p.primesOver B := Ideal.primesOver.mk PX
  let qY : p.primesOver B := Ideal.primesOver.mk PY
  let qZ : p.primesOver B := Ideal.primesOver.mk PZ
  have hqXY : qX ≠ qY := by
    intro h
    exact hXY (by
      simpa [qX, qY] using
        congrArg (fun Q : p.primesOver B => Q.1) h)
  have hqXZ : qX ≠ qZ := by
    intro h
    exact hXZ (by
      simpa [qX, qZ] using
        congrArg (fun Q : p.primesOver B => Q.1) h)
  have hqYZ : qY ≠ qZ := by
    intro h
    exact hYZ (by
      simpa [qY, qZ] using
        congrArg (fun Q : p.primesOver B => Q.1) h)
  have hcover : ∀ Q : p.primesOver B,
      Q = qX ∨ Q = qY ∨ Q = qZ := by
    intro Q
    rcases hclass Q with h | h | h
    · left
      apply Subtype.ext
      simpa [qX] using h
    · right; left
      apply Subtype.ext
      simpa [qY] using h
    · right; right
      apply Subtype.ext
      simpa [qZ] using h
  let e : Fin 3 ≃ p.primesOver B :=
    Equiv.ofBijective (fin3Enum qX qY qZ)
      (fin3Enum_bijective qX qY qZ hqXY hqXZ hqYZ hcover)
  have he0 : e (0 : Fin 3) = qX := by rfl
  have he1 : e (1 : Fin 3) = qY := by rfl
  have he2 : e (2 : Fin 3) = qZ := by rfl
  calc
    (∑ Q : p.primesOver B, f Q) =
        ∑ i : Fin 3, f (e i) := by
      refine Finset.sum_equiv e.symm ?_ ?_
      · intro Q
        simp
      · intro Q hQ
        simp
    _ = f (Ideal.primesOver.mk PX) +
          f (Ideal.primesOver.mk PY) +
          f (Ideal.primesOver.mk PZ) := by
      rw [Fin.sum_univ_three, he0, he1, he2]
      rfl

theorem sum_primesOver_val_eq_three
    [Fintype (p.primesOver B)]
    {M : Type*} [AddCommMonoid M]
    (hXY : PX ≠ PY) (hXZ : PX ≠ PZ) (hYZ : PY ≠ PZ)
    (hclass : ∀ Q : p.primesOver B,
      Q.1 = PX ∨ Q.1 = PY ∨ Q.1 = PZ)
    (g : Ideal B → M) :
    (∑ Q : p.primesOver B, g Q.1) =
      g PX + g PY + g PZ := by
  simpa using
    sum_primesOver_eq_three p PX PY PZ hXY hXZ hYZ hclass
      (fun Q => g Q.1)

end PrimesOver

end Q6827Check
