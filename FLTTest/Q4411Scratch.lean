import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open Ideal

variable {A : Type*} [CommRing A]

namespace Q4411Scratch

noncomputable def mumfordIdeal (U V Y : A) : Ideal A :=
  Ideal.span {U, Y - V}

noncomputable def mumfordConjIdeal (U V Y : A) : Ideal A :=
  Ideal.span {U, Y + V}

noncomputable def uIdeal (U : A) : Ideal A :=
  Ideal.span {U}

lemma mumfordIdeal_mul_conj
    (U V W Y a b c : A)
    (hrel : (Y - V) * (Y + V) = U * W)
    (hbez : a * U + b * (2 * V) + c * W = 1) :
    mumfordIdeal U V Y * mumfordConjIdeal U V Y = uIdeal U := by
  rw [mumfordIdeal, mumfordConjIdeal, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [uIdeal, Ideal.mem_span_singleton]
      exact ⟨U, by ring⟩
    · rw [uIdeal, Ideal.mem_span_singleton]
      exact ⟨Y + V, by ring⟩
    · rw [uIdeal, Ideal.mem_span_singleton]
      exact ⟨Y - V, by ring⟩
    · rw [hrel, uIdeal, Ideal.mem_span_singleton]
      exact ⟨W, rfl⟩
  · rw [uIdeal, Ideal.span_singleton_le_iff_mem]
    let J : Ideal A :=
      Ideal.span {U * U, U * (Y + V), (Y - V) * U, (Y - V) * (Y + V)}
    change U ∈ J
    have hUU : U * U ∈ J := Ideal.subset_span (by simp [J])
    have hUp : U * (Y + V) ∈ J := Ideal.subset_span (by simp [J])
    have hUm : (Y - V) * U ∈ J := Ideal.subset_span (by simp [J])
    have hLast : (Y - V) * (Y + V) ∈ J := Ideal.subset_span (by simp [J])
    have hU2V : U * (2 * V) ∈ J := by
      have := J.sub_mem hUp hUm
      convert this using 1 <;> ring
    have hUW : U * W ∈ J := by
      rw [← hrel]
      exact hLast
    have hsum : a * (U * U) + b * (U * (2 * V)) + c * (U * W) ∈ J :=
      J.add_mem (J.add_mem (J.mul_mem_left a hUU) (J.mul_mem_left b hU2V))
        (J.mul_mem_left c hUW)
    convert hsum using 1
    calc
      a * (U * U) + b * (U * (2 * V)) + c * (U * W) =
          U * (a * U + b * (2 * V) + c * W) := by ring
      _ = U := by rw [hbez, mul_one]

end Q4411Scratch
