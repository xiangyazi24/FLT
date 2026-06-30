# Q2620 / Q2617: AP root-step gcd lemmas

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.
Namespace: `MazurProof.RationalPointsN12`.

Below is a compact `IsCoprime` proof route. It avoids the Nat-prime divisor criterion entirely. The idea is:

```text
gcd(u,v)=1 -> IsCoprime u v -> IsCoprime u v^2.
v^2 = u^2 + 4N, so IsCoprime u (u^2+4N).
Remove the u^2 term, then remove the factor 4: IsCoprime u N.
```

For the right-root version, use `u^2 = v^2 - 4N`, remove the `v^2` term to get coprime to `-4N`, flip the sign by an explicit Bezout witness, then remove `4`.

If these imports are not already available through the file’s current imports, add the first one. The tactics are usually already imported in this file family.

```lean
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
```

Code to place after the checked gap lemmas:

```lean
namespace MazurProof.RationalPointsN12

theorem gcd_left_step_of_adjacent_square_gap {u v N : Int}
    (huv : Int.gcd u v = 1)
    (hgap : v ^ 2 - u ^ 2 = 4 * N) : Int.gcd u N = 1 := by
  have huvC : IsCoprime u v := Int.isCoprime_iff_gcd_eq_one.mpr huv
  have huv2 : IsCoprime u (v ^ 2) := by
    exact huvC.pow_right
  have hv2' : v ^ 2 = 4 * N + u ^ 2 := by
    nlinarith [hgap]
  have hv2 : v ^ 2 = 4 * N + u * u := by
    calc
      v ^ 2 = 4 * N + u ^ 2 := hv2'
      _ = 4 * N + u * u := by ring
  have hcop : IsCoprime u (4 * N + u * u) := by
    simpa [hv2] using huv2
  have h4N : IsCoprime u (4 * N) := hcop.of_add_mul_left_right
  have hN : IsCoprime u N := h4N.of_mul_right_right
  exact Int.isCoprime_iff_gcd_eq_one.mp hN

theorem gcd_right_step_of_adjacent_square_gap {u v N : Int}
    (huv : Int.gcd u v = 1)
    (hgap : v ^ 2 - u ^ 2 = 4 * N) : Int.gcd v N = 1 := by
  have hvuC : IsCoprime v u := (Int.isCoprime_iff_gcd_eq_one.mpr huv).symm
  have hvu2 : IsCoprime v (u ^ 2) := by
    exact hvuC.pow_right
  have hu2' : u ^ 2 = -4 * N + v ^ 2 := by
    nlinarith [hgap]
  have hu2 : u ^ 2 = -4 * N + v * v := by
    calc
      u ^ 2 = -4 * N + v ^ 2 := hu2'
      _ = -4 * N + v * v := by ring
  have hcop : IsCoprime v (-4 * N + v * v) := by
    simpa [hu2] using hvu2
  have hneg4N : IsCoprime v (-4 * N) := hcop.of_add_mul_left_right
  have h4N : IsCoprime v (4 * N) := by
    rcases hneg4N with ⟨a, b, hab⟩
    refine ⟨a, -b, ?_⟩
    rw [← hab]
    ring
  have hN : IsCoprime v N := h4N.of_mul_right_right
  exact Int.isCoprime_iff_gcd_eq_one.mp hN

/-- `p` is coprime to the AP step `N`, using the `p,q` gap. -/
theorem primitiveCentered_p_coprime_N (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.p S.N = 1 := by
  exact gcd_left_step_of_adjacent_square_gap S.hpq (primitiveCentered_gap_pq S)

/-- `q` is coprime to the AP step `N`, using the `p,q` gap. -/
theorem primitiveCentered_q_coprime_N (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.q S.N = 1 := by
  exact gcd_right_step_of_adjacent_square_gap S.hpq (primitiveCentered_gap_pq S)

/-- `r` is coprime to the AP step `N`, using the `q,r` gap. -/
theorem primitiveCentered_r_coprime_N (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.r S.N = 1 := by
  exact gcd_right_step_of_adjacent_square_gap S.hqr (primitiveCentered_gap_qr S)

/-- `s` is coprime to the AP step `N`, using the `r,s` gap. -/
theorem primitiveCentered_s_coprime_N (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.s S.N = 1 := by
  exact gcd_right_step_of_adjacent_square_gap S.hrs (primitiveCentered_gap_rs S)

/-- Same as `primitiveCentered_p_coprime_N`, in `IsCoprime` form. -/
theorem primitiveCentered_p_isCoprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.p S.N := by
  exact Int.isCoprime_iff_gcd_eq_one.mpr (primitiveCentered_p_coprime_N S)

/-- Same as `primitiveCentered_q_coprime_N`, in `IsCoprime` form. -/
theorem primitiveCentered_q_isCoprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.q S.N := by
  exact Int.isCoprime_iff_gcd_eq_one.mpr (primitiveCentered_q_coprime_N S)

/-- Same as `primitiveCentered_r_coprime_N`, in `IsCoprime` form. -/
theorem primitiveCentered_r_isCoprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.r S.N := by
  exact Int.isCoprime_iff_gcd_eq_one.mpr (primitiveCentered_r_coprime_N S)

/-- Same as `primitiveCentered_s_coprime_N`, in `IsCoprime` form. -/
theorem primitiveCentered_s_isCoprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.s S.N := by
  exact Int.isCoprime_iff_gcd_eq_one.mpr (primitiveCentered_s_coprime_N S)

end MazurProof.RationalPointsN12
```

Notes:

* The wrappers above use only adjacent gcd fields: `hpq`, `hqr`, and `hrs`.
* The theorem statements use `Int.gcd root N = 1`, matching the requested orientation. If a later lemma wants `IsCoprime S.N S.p`, use `(primitiveCentered_p_isCoprime_N S).symm`.
* No Nat-prime API is needed for this layer. If you later choose the prime-divisor route, the relevant APIs are `Nat.Prime.not_coprime_iff_dvd`, `Int.natCast_dvd`, and `Int.Prime.dvd_natAbs_of_coe_dvd_sq`.
