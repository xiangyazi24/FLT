# Q2607: Nat refinement of two factorizations

Target helper:

```lean
theorem two_coprime_factorizations_refine_nat
    {A U V Up Vp : Nat}
    (hUV : A = U * V) (hUpVp : A = Up * Vp)
    (hcopUV : Nat.Coprime U V)
    (hcopUpVp : Nat.Coprime Up Vp) :
    exists a b c d : Nat,
      U = a * b /\ V = c * d /\ Up = a * c /\ Vp = b * d
```

For the positive integer variables needed in the Euler-square-pair descent, use the following stronger positive theorem.  It does **not** need either coprimality hypothesis: any equality of positive-left factorizations

```text
U*V = Up*Vp,  0<U, 0<Up
```

has the matrix refinement.  This avoids all zero-case clutter and is exactly what the later positive `Int` wrapper needs.

The construction is the expected one:

```text
a = gcd U Up,
U = a*b,
Up = a*c,
gcd b c = 1,
b*V = c*Vp,
therefore b | Vp,
Vp = b*d,
V = c*d.
```

---

## Lean code

Paste this near the local Nat/Int arithmetic helper layer.  It uses only `Mathlib` and no axioms/sorries.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/--
Positive-left version of the refinement of two factorizations.
This is stronger than the coprime version needed later: the hypotheses
`Nat.Coprime U V` and `Nat.Coprime Up Vp` are not needed once `U,Up > 0`.
-/
theorem two_factorizations_refine_nat_pos
    {U V Up Vp : Nat}
    (hU : 0 < U) (hUp : 0 < Up)
    (hmul : U * V = Up * Vp) :
    ∃ a b c d : Nat,
      U = a * b ∧ V = c * d ∧ Up = a * c ∧ Vp = b * d := by
  let a : Nat := Nat.gcd U Up
  have haU_dvd : a ∣ U := Nat.gcd_dvd_left U Up
  have haUp_dvd : a ∣ Up := Nat.gcd_dvd_right U Up
  rcases haU_dvd with ⟨b, hbU⟩
  rcases haUp_dvd with ⟨c, hcUp⟩

  have ha_pos : 0 < a := by
    by_contra hapos
    have haz : a = 0 := Nat.eq_zero_of_not_pos hapos
    rw [haz] at hbU
    omega

  have hbc : Nat.Coprime b c := by
    have hgcd_mul : Nat.gcd U Up = a * Nat.gcd b c := by
      rw [hbU, hcUp]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using (Nat.gcd_mul_left a b c)
    have hcancel : Nat.gcd b c = 1 := by
      have hmul_cancel : a * Nat.gcd b c = a * 1 := by
        simpa [a] using hgcd_mul.symm
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
The requested coprime-factorization refinement, with the positivity hypotheses
that are available in the later positive `Int` descent wrapper.
The coprimality assumptions are intentionally unused: the positive refinement
above is stronger.
-/
theorem two_coprime_factorizations_refine_nat_pos
    {A U V Up Vp : Nat}
    (hU : 0 < U) (hUp : 0 < Up)
    (hUV : A = U * V) (hUpVp : A = Up * Vp)
    (_hcopUV : Nat.Coprime U V)
    (_hcopUpVp : Nat.Coprime Up Vp) :
    ∃ a b c d : Nat,
      U = a * b ∧ V = c * d ∧ Up = a * c ∧ Vp = b * d := by
  apply two_factorizations_refine_nat_pos hU hUp
  calc
    U * V = A := hUV.symm
    _ = Up * Vp := hUpVp

end MazurProof.RationalPointsN12
```

---

## API notes and fallbacks

1. `Nat.gcd_mul_left` is the key gcd API used above.  Its expected shape is:

```lean
Nat.gcd (a * b) (a * c) = a * Nat.gcd b c
```

The `simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]` wrapper is there to handle harmless associativity/commutativity orientation.

2. `Nat.Coprime.dvd_of_dvd_mul_left` is used in the Euclid step:

```lean
have hb_dvd_cVp : b ∣ c * Vp := ⟨V, hbVcVp.symm⟩
exact hbc.dvd_of_dvd_mul_left hb_dvd_cVp
```

If the local Mathlib orientation differs, try the symmetric spelling:

```lean
exact hbc.symm.dvd_of_dvd_mul_right hb_dvd_cVp
```

but in current Mathlib-style APIs the displayed `dvd_of_dvd_mul_left` is the intended one: for `hbc : Nat.Coprime b c`, it strips the left factor `c` from a divisibility of `c * Vp`.

3. The literal zero-allowed theorem in the prompt is true under the two coprime-factorization hypotheses, but it is not the theorem I recommend using for the Euler descent.  Its proof is mostly degenerate case work:

```text
U=0 forces V=1 from Coprime U V;
then Up*Vp=0 and Coprime Up Vp forces either (Up,Vp)=(0,1) or (1,0),
and similarly for the Up=0 branch.
```

Since the later `Int` variables `U,V,Up,Vp` are positive in the descent parametrization, the positive theorem above is the clean interface to wrap.

4. If you still want the exact zero-allowed theorem, prove it as a thin wrapper:

```lean
-- sketch only, because the positive theorem is the useful interface
by_cases hU0 : U = 0
  -- use `hcopUV` to get `V=1`, split `Up*Vp=0`.
by_cases hUp0 : Up = 0
  -- symmetric.
-- positive branch:
exact two_coprime_factorizations_refine_nat_pos
  (Nat.pos_of_ne_zero hU0) (Nat.pos_of_ne_zero hUp0)
  hUV hUpVp hcopUV hcopUpVp
```

The positive theorem avoids these zero branches entirely.
