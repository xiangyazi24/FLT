# Q2610: exact Nat factorization refinement helper

This answers only the Nat factor-refinement problem.

The clean proof is to first prove a positive-left refinement that does **not** require coprimality of `U,V` and `Up,Vp`, then wrap the exact theorem by handling the degenerate zero cases using the two `Nat.Coprime` hypotheses.

The positive construction is:

```text
a = gcd U Up,
U = a*b,
Up = a*c,
gcd b c = 1,
b*V = c*Vp,
b | Vp,
Vp = b*d,
V = c*d.
```

The exact theorem in the prompt is true, but the zero cases are real.  For example, `U=0` forces `V=1` from `Nat.Coprime U V`, and then `Up*Vp=0`; the second coprimality condition forces either `(Up,Vp)=(0,1)` or `(1,0)`.

---

## Lean code

Paste under `import Mathlib.Tactic` in the current namespace.  No `sorry`, no axioms.

```lean
import Mathlib.Tactic

/--
Positive-left refinement of two factorizations.
This is the main theorem used in positive `Int` wrappers.
It does not require `Nat.Coprime U V` or `Nat.Coprime Up Vp`.
-/
theorem two_factorizations_refine_nat_pos
    {U V Up Vp : Nat}
    (hU : 0 < U) (hUp : 0 < Up)
    (hmul : U * V = Up * Vp) :
    ∃ a b c d : Nat,
      U = a * b ∧ V = c * d ∧ Up = a * c ∧ Vp = b * d := by
  let a : Nat := Nat.gcd U Up
  have haU_dvd : a ∣ U := by
    simpa [a] using Nat.gcd_dvd_left U Up
  have haUp_dvd : a ∣ Up := by
    simpa [a] using Nat.gcd_dvd_right U Up
  rcases haU_dvd with ⟨b, hbU⟩
  rcases haUp_dvd with ⟨c, hcUp⟩

  have ha_pos : 0 < a := by
    by_contra hapos
    have haz : a = 0 := Nat.eq_zero_of_not_pos hapos
    rw [haz] at hbU
    omega

  have hbc : Nat.Coprime b c := by
    have hgcd_mul : a * Nat.gcd b c = a := by
      calc
        a * Nat.gcd b c = Nat.gcd (a * b) (a * c) := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            using (Nat.gcd_mul_left a b c).symm
        _ = Nat.gcd U Up := by rw [← hbU, ← hcUp]
        _ = a := rfl
    have hcancel : Nat.gcd b c = 1 := by
      have hmul_cancel : a * Nat.gcd b c = a * 1 := by
        simpa using hgcd_mul
      exact mul_left_cancel₀ (Nat.ne_of_gt ha_pos) hmul_cancel
    simpa [Nat.Coprime] using hcancel

  have hbVcVp : b * V = c * Vp := by
    have hmain : a * (b * V) = a * (c * Vp) := by
      calc
        a * (b * V) = (a * b) * V := by ring
        _ = U * V := by rw [← hbU]
        _ = Up * Vp := hmul
        _ = (a * c) * Vp := by rw [hcUp]
        _ = a * (c * Vp) := by ring
    exact mul_left_cancel₀ (Nat.ne_of_gt ha_pos) hmain

  have hb_pos : 0 < b := by
    by_contra hbpos
    have hbz : b = 0 := Nat.eq_zero_of_not_pos hbpos
    rw [hbz] at hbU
    omega

  have hb_dvd_Vp : b ∣ Vp := by
    have hb_dvd_cVp : b ∣ c * Vp := ⟨V, hbVcVp.symm⟩
    exact hbc.dvd_of_dvd_mul_left hb_dvd_cVp

  rcases hb_dvd_Vp with ⟨d, hVp⟩

  have hV : V = c * d := by
    have hmul_b : b * V = b * (c * d) := by
      calc
        b * V = c * Vp := hbVcVp
        _ = c * (b * d) := by rw [hVp]
        _ = b * (c * d) := by ring
    exact mul_left_cancel₀ (Nat.ne_of_gt hb_pos) hmul_b

  exact ⟨a, b, c, d, hbU, hV, hcUp, hVp⟩

/--
The exact zero-allowed theorem requested in Q2610.
The coprimality hypotheses are only needed in the zero cases.
-/
theorem two_coprime_factorizations_refine_nat
    {A U V Up Vp : Nat}
    (hUV : A = U * V) (hUpVp : A = Up * Vp)
    (hcopUV : Nat.Coprime U V)
    (hcopUpVp : Nat.Coprime Up Vp) :
    ∃ a b c d : Nat,
      U = a * b ∧ V = c * d ∧ Up = a * c ∧ Vp = b * d := by
  by_cases hU0 : U = 0
  · have hV1 : V = 1 := by
      simpa [Nat.Coprime, hU0] using hcopUV
    have hA0 : A = 0 := by
      simp [hUV, hU0]
    have hUpVp0 : Up * Vp = 0 := by
      have h : Up * Vp = A := hUpVp.symm
      simpa [hA0] using h
    rcases (mul_eq_zero.mp hUpVp0) with hUp0 | hVp0
    · have hVp1 : Vp = 1 := by
        simpa [Nat.Coprime, hUp0] using hcopUpVp
      refine ⟨0, 1, 1, 1, ?_, ?_, ?_, ?_⟩
      · simp [hU0]
      · simp [hV1]
      · simp [hUp0]
      · simp [hVp1]
    · have hUp1 : Up = 1 := by
        simpa [Nat.Coprime, hVp0] using hcopUpVp
      refine ⟨1, 0, 1, 1, ?_, ?_, ?_, ?_⟩
      · simp [hU0]
      · simp [hV1]
      · simp [hUp1]
      · simp [hVp0]
  · by_cases hUp0 : Up = 0
    · have hVp1 : Vp = 1 := by
        simpa [Nat.Coprime, hUp0] using hcopUpVp
      have hA0 : A = 0 := by
        simp [hUpVp, hUp0]
      have hUV0 : U * V = 0 := by
        have h : U * V = A := hUV.symm
        simpa [hA0] using h
      have hV0 : V = 0 := by
        rcases (mul_eq_zero.mp hUV0) with hUz | hVz
        · exact False.elim (hU0 hUz)
        · exact hVz
      have hU1 : U = 1 := by
        simpa [Nat.Coprime, hV0] using hcopUV
      refine ⟨1, 1, 0, 1, ?_, ?_, ?_, ?_⟩
      · simp [hU1]
      · simp [hV0]
      · simp [hUp0]
      · simp [hVp1]
    · apply two_factorizations_refine_nat_pos
      · exact Nat.pos_of_ne_zero hU0
      · exact Nat.pos_of_ne_zero hUp0
      · calc
          U * V = A := hUV.symm
          _ = Up * Vp := hUpVp
```

---

## API notes

The Euclid step used above is:

```lean
hbc.dvd_of_dvd_mul_left : b ∣ c * Vp → b ∣ Vp
```

for `hbc : Nat.Coprime b c`.

If a local Mathlib snapshot has the orientation named differently, replace the single line

```lean
exact hbc.dvd_of_dvd_mul_left hb_dvd_cVp
```

by one of these equivalent spellings:

```lean
exact Nat.Coprime.dvd_of_dvd_mul_left hbc hb_dvd_cVp
```

or, if only the right-stripping theorem is available:

```lean
exact hbc.symm.dvd_of_dvd_mul_right hb_dvd_cVp
```

The zero split uses generic `mul_eq_zero.mp`; if your environment prefers the Nat namespace spelling, use:

```lean
Nat.mul_eq_zero.mp hUpVp0
Nat.mul_eq_zero.mp hUV0
```

but current Mathlib under `import Mathlib.Tactic` should accept `mul_eq_zero.mp`.
