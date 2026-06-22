import scratch.WardGapInduction

/-!
# Unconditional Ward's theorem: `IsEllSequence (normEDS b c d)` over ANY `CommRing`

The conditional version (`normEDS_isEllSequence_of_nonvanishing`, WardGapInduction) needs a domain
with non-vanishing values. To drop that, we establish the universal-ring nonvanishing via the
**identity-sequence specialization** `(b,c,d) = (2,3,2)`, for which `normEDS 2 3 2 j = j` (so every
term is non-zero for `j≠0`). Then `AddRel` over the universal domain `MvPolynomial (Fin 3) ℤ`
transports to every `CommRing` by the ring-hom naturality of `normEDS` (`map_normEDS`).

Specialization trick: ChatGPT (dm1, git-drop). Verified numerically + the two `ring` identities below.
-/

namespace FLT.EDS

open MvPolynomial

variable {R : Type*} [CommRing R]

lemma odd_poly_232 (n : ℤ) : (n + 2) * n ^ 3 - (n - 1) * (n + 1) ^ 3 = 2 * n + 1 := by ring

lemma even_poly_232 (n : ℤ) :
    n * ((n + 2) * (n - 1) ^ 2 - (n - 2) * (n + 1) ^ 2) = 4 * n := by ring

/-- `normEDS 2 3 2` is the identity sequence on `ℕ` (strong induction, parity split). -/
lemma normEDS_232_nat (n : ℕ) : normEDS (2 : ℤ) 3 2 (n : ℤ) = (n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [normEDS_zero]
    | 1 => simp [normEDS_one]
    | 2 => simp [normEDS_two]
    | 3 => simp [normEDS_three]
    | 4 => simp [normEDS_four]
    | (k + 5) =>
      rcases Nat.even_or_odd (k + 5) with ⟨q, hq⟩ | ⟨q, hq⟩
      · -- even: k+5 = q+q = 2q, q ≥ 3
        have key := normEDS_even (2 : ℤ) 3 2 (q : ℤ)
        have c2 : normEDS (2:ℤ) 3 2 ((q:ℤ) - 2) = (q:ℤ) - 2 := by
          have := ih (q - 2) (by omega); rwa [Nat.cast_sub (by omega), Nat.cast_ofNat] at this
        have c1 : normEDS (2:ℤ) 3 2 ((q:ℤ) - 1) = (q:ℤ) - 1 := by
          have := ih (q - 1) (by omega); rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
        have c0 : normEDS (2:ℤ) 3 2 (q:ℤ) = (q:ℤ) := ih q (by omega)
        have p1 : normEDS (2:ℤ) 3 2 ((q:ℤ) + 1) = (q:ℤ) + 1 := by
          have := ih (q + 1) (by omega); rwa [Nat.cast_add, Nat.cast_one] at this
        have p2 : normEDS (2:ℤ) 3 2 ((q:ℤ) + 2) = (q:ℤ) + 2 := by
          have := ih (q + 2) (by omega); rwa [Nat.cast_add, Nat.cast_ofNat] at this
        rw [c2, c1, c0, p1, p2] at key
        have hgoal : normEDS (2:ℤ) 3 2 (2 * (q:ℤ)) * 2 = (2 * (q:ℤ)) * 2 := by
          rw [key]; linear_combination even_poly_232 (q:ℤ)
        have hfin : normEDS (2:ℤ) 3 2 (2 * (q:ℤ)) = 2 * (q:ℤ) :=
          mul_right_cancel₀ (by norm_num : (2:ℤ) ≠ 0) hgoal
        rw [show ((k + 5 : ℕ) : ℤ) = 2 * (q:ℤ) by push_cast; omega]; exact hfin
      · -- odd: k+5 = 2q+1, q ≥ 2
        have key := normEDS_odd (2 : ℤ) 3 2 (q : ℤ)
        have c1 : normEDS (2:ℤ) 3 2 ((q:ℤ) - 1) = (q:ℤ) - 1 := by
          have := ih (q - 1) (by omega); rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
        have c0 : normEDS (2:ℤ) 3 2 (q:ℤ) = (q:ℤ) := ih q (by omega)
        have p1 : normEDS (2:ℤ) 3 2 ((q:ℤ) + 1) = (q:ℤ) + 1 := by
          have := ih (q + 1) (by omega); rwa [Nat.cast_add, Nat.cast_one] at this
        have p2 : normEDS (2:ℤ) 3 2 ((q:ℤ) + 2) = (q:ℤ) + 2 := by
          have := ih (q + 2) (by omega); rwa [Nat.cast_add, Nat.cast_ofNat] at this
        rw [c1, c0, p1, p2] at key
        rw [show ((k + 5 : ℕ) : ℤ) = 2 * (q:ℤ) + 1 by push_cast; omega, key]
        linear_combination odd_poly_232 (q:ℤ)

/-- `normEDS 2 3 2` is the identity sequence on all of `ℤ`. -/
lemma normEDS_232_eq_id (j : ℤ) : normEDS (2 : ℤ) 3 2 j = j := by
  rcases lt_or_ge j 0 with hj | hj
  · have h := normEDS_232_nat (-j).toNat
    rw [Int.toNat_of_nonneg (by omega)] at h
    rw [show j = -(-j) by ring, normEDS_neg, h]
  · lift j to ℕ using hj with n; exact_mod_cast normEDS_232_nat n

/-- Universal-ring nonvanishing: `normEDS (X 0) (X 1) (X 2) j ≠ 0` for `j ≠ 0`. -/
lemma universal_normEDS_ne_zero {j : ℤ} (hj : j ≠ 0) :
    normEDS (X 0 : MvPolynomial (Fin 3) ℤ) (X 1) (X 2) j ≠ 0 := by
  intro hzero
  have h := congrArg (eval₂Hom (Int.castRingHom ℤ) ![2, 3, 2]) hzero
  simp only [map_normEDS, map_zero, eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, normEDS_232_eq_id] at h
  exact hj h

/-- **Ward's addition formula, unconditional.** `AddRel (normEDS b c d) m n` over any `CommRing`. -/
theorem normEDS_addRel (b c d : R) (m n : ℤ) : AddRel (normEDS b c d) m n := by
  have hU := normEDS_addRel_of_nonvanishing (X 0 : MvPolynomial (Fin 3) ℤ) (X 1) (X 2)
    (X_ne_zero 1) (fun j hj => universal_normEDS_ne_zero hj) m n
  unfold AddRel at hU ⊢
  have key := congrArg (eval₂Hom (Int.castRingHom R) ![b, c, d]) hU
  simpa only [map_sub, map_mul, map_pow, map_normEDS, eval₂Hom_X', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] using key

/-- **Ward's theorem, unconditional** (the open Mathlib TODO): `normEDS b c d` is an elliptic
sequence over every commutative ring. -/
theorem normEDS_isEllSequence (b c d : R) : IsEllSequence (normEDS b c d) :=
  isEllSequence_of_addRel (fun m n => normEDS_addRel b c d m n)

end FLT.EDS
