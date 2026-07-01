# Q2740: reduced rational-slope code for primitive Eisenstein triples

Target namespace: `MazurProof.RationalPointsN12`.

The code below assumes the existing local definition

```lean
def EisensteinTriple (X Y Z : ℤ) : Prop :=
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2
```

Paste the following after that definition. The only nontrivial inequality is `Y < Z + X`; it is proved from

```lean
Z ^ 2 - (Y - X) ^ 2 = X * Y > 0
```

and `abs_lt_of_sq_lt_sq`.

## API inventory

```lean
#check abs_lt_of_sq_lt_sq
#check Rat.num_pos
#check Rat.num_lt_denom_iff
#check Rat.num_div_den
#check Rat.reduced
#check Rat.intCast_injective
#check Int.isCoprime_iff_gcd_eq_one
```

If your checkout has renamed the rational reconstruction lemma, replace

```lean
(Rat.num_div_den q).symm
```

by the local equivalent, usually one of:

```lean
(Rat.num_divInt_den q).symm
q.num_divInt_den.symm
```

## Drop-in Lean code

```lean
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

noncomputable def eisensteinSlope (X Y Z : ℤ) : ℚ :=
  (Y : ℚ) / (Z + X : ℤ)

noncomputable def eisenstein_m (X Y Z : ℤ) : ℤ :=
  ((eisensteinSlope X Y Z).den : ℤ)

noncomputable def eisenstein_n (X Y Z : ℤ) : ℤ :=
  (eisensteinSlope X Y Z).num

lemma eisenstein_Z_add_X_pos {X Y Z : ℤ}
    (hX : 0 < X) (hZ : 0 < Z) :
    0 < Z + X := by
  nlinarith

lemma eisenstein_Y_lt_Z_add_X {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hE : EisensteinTriple X Y Z) :
    Y < Z + X := by
  have hsq_lt : (Y - X) ^ 2 < Z ^ 2 := by
    have hdiff : Z ^ 2 - (Y - X) ^ 2 = X * Y := by
      unfold EisensteinTriple at hE
      rw [hE]
      ring
    have hxypos : 0 < X * Y := mul_pos hX hY
    nlinarith
  have habs : |Y - X| < Z :=
    abs_lt_of_sq_lt_sq hsq_lt (le_of_lt hZ)
  have hYXlt : Y - X < Z :=
    lt_of_le_of_lt (le_abs_self (Y - X)) habs
  nlinarith

lemma eisenstein_slope_pos_lt_one {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hE : EisensteinTriple X Y Z) :
    0 < (Y : ℚ) / (Z + X : ℤ) ∧
      (Y : ℚ) / (Z + X : ℤ) < 1 := by
  have hdenZ : 0 < Z + X := eisenstein_Z_add_X_pos hX hZ
  have hdenQ : (0 : ℚ) < ((Z + X : ℤ) : ℚ) := by
    exact_mod_cast hdenZ
  have hYQ : (0 : ℚ) < (Y : ℚ) := by
    exact_mod_cast hY
  have hYltZ : Y < Z + X := eisenstein_Y_lt_Z_add_X hX hY hZ hE
  have hYltQ : (Y : ℚ) < ((Z + X : ℤ) : ℚ) := by
    exact_mod_cast hYltZ
  constructor
  · exact div_pos hYQ hdenQ
  · calc
      (Y : ℚ) / ((Z + X : ℤ) : ℚ)
          < ((Z + X : ℤ) : ℚ) / ((Z + X : ℤ) : ℚ) := by
            exact div_lt_div_of_pos_right hYltQ hdenQ
      _ = 1 := by
            exact div_self (ne_of_gt hdenQ)

lemma eisenstein_mn_pos_coprime {X Y Z : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hE : EisensteinTriple X Y Z) :
    0 < eisenstein_n X Y Z ∧
      eisenstein_n X Y Z < eisenstein_m X Y Z ∧
      IsCoprime (eisenstein_m X Y Z) (eisenstein_n X Y Z) := by
  let q : ℚ := eisensteinSlope X Y Z
  have hq : 0 < q ∧ q < 1 := by
    simpa [q, eisensteinSlope] using
      eisenstein_slope_pos_lt_one hX hY hZ hE
  have hnpos : 0 < q.num :=
    (Rat.num_pos (a := q)).2 hq.1
  have hnltm : q.num < (q.den : ℤ) :=
    (Rat.num_lt_denom_iff (q := q)).2 hq.2
  have hcop_gcd : Int.gcd ((q.den : ℤ)) q.num = 1 := by
    rw [Int.gcd_comm]
    exact q.reduced
  have hcop : IsCoprime ((q.den : ℤ)) q.num :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcop_gcd
  exact ⟨by simpa [eisenstein_n, q] using hnpos,
    by simpa [eisenstein_m, eisenstein_n, q] using hnltm,
    by simpa [eisenstein_m, eisenstein_n, q] using hcop⟩

/-- Cross multiplication for the reduced slope.

No Eisenstein equation is needed here; only `0 < Z + X`, supplied by `hX,hZ`, is used to keep the
slope denominator nonzero. -/
lemma eisenstein_mn_cross_mul {X Y Z : ℤ}
    (hX : 0 < X) (hZ : 0 < Z) :
    eisenstein_m X Y Z * Y = eisenstein_n X Y Z * (Z + X) := by
  let q : ℚ := eisensteinSlope X Y Z
  have hdenZ : 0 < Z + X := eisenstein_Z_add_X_pos hX hZ
  have hdenQ : (0 : ℚ) < ((Z + X : ℤ) : ℚ) := by
    exact_mod_cast hdenZ
  have hden_ne_Q : (((Z + X : ℤ) : ℚ)) ≠ 0 := ne_of_gt hdenQ
  have hqden_pos_Q : (0 : ℚ) < (q.den : ℚ) := by
    exact_mod_cast (Rat.pos q)
  have hqden_ne_Q : (q.den : ℚ) ≠ 0 := ne_of_gt hqden_pos_Q
  have hqeq :
      (Y : ℚ) / ((Z + X : ℤ) : ℚ) = (q.num : ℚ) / (q.den : ℚ) := by
    simpa [q, eisensteinSlope] using (Rat.num_div_den q).symm
  have hcrossQ :
      (Y : ℚ) * (q.den : ℚ) =
        (q.num : ℚ) * ((Z + X : ℤ) : ℚ) := by
    field_simp [hden_ne_Q, hqden_ne_Q] at hqeq
    simpa [mul_comm, mul_left_comm, mul_assoc] using hqeq
  have hcrossZ : Y * (q.den : ℤ) = q.num * (Z + X) := by
    apply Rat.intCast_injective
    norm_cast
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcrossQ
  simpa [eisenstein_m, eisenstein_n, q, mul_comm, mul_left_comm, mul_assoc] using hcrossZ

end MazurProof.RationalPointsN12
```

## If `field_simp` is too aggressive in your local checkout

Replace the proof of `hcrossQ` by this equivalent version; it uses the same nonzero-denominator facts but keeps rewriting local:

```lean
  have hcrossQ :
      (Y : ℚ) * (q.den : ℚ) =
        (q.num : ℚ) * ((Z + X : ℤ) : ℚ) := by
    have h := hqeq
    field_simp [hden_ne_Q, hqden_ne_Q] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
```

The rest of `eisenstein_mn_cross_mul` is unchanged.
