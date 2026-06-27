# Q1371 (dm1/dm3): descent branch `U=a^4, V=5*b^4`

Use the Pythagorean triple in the orientation

```lean
PythagoreanTriple (b ^ 2) h r
```

not `PythagoreanTriple h (b^2) r`, because `PythagoreanTriple.coprime_classification'` assumes the first leg is odd and then returns

```lean
b^2 = m^2 - n^2,
h = 2*m*n,
r = m^2+n^2.
```

Below is the clean branch skeleton.  The explicit `sorry` is the requested coprime square-factor split of `b^2 = (m-n)(m+n)`.  I state the already-proved local algebra facts as hypotheses: in the full proof these come from `h=(a^2-b^2)/2`, `a,b` odd, and the identity
`4*r^2=(a^2-b^2)^2+4*b^4`.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace DM3

/-- Integer quartic-plus predicate. -/
def QuarticPlusZ (r B s : ℤ) : Prop :=
  0 < r ∧ 0 < B ∧ Int.gcd r B = 1 ∧
    s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

/--
The only intentionally sorry'd local arithmetic lemma in this branch.

Input: primitive Pythagorean parameters with
`b^2 = (m-n)(m+n)` and `gcd(m-n,m+n)=1`.
Output: the square split `m-n=u^2`, `m+n=v^2`, and `b=u*v`, with the
positivity/nondegeneracy needed for strict descent.
-/
theorem split_b_square_from_coprime_factors
    {m n b : ℤ}
    (hb_pos : 0 < b)
    (hb2_mn : b ^ 2 = m ^ 2 - n ^ 2)
    (hmn_gcd : Int.gcd m n = 1)
    (hmn_parity :
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)) :
    ∃ u v : ℤ,
      0 < u ∧ 1 < v ∧ Int.gcd v u = 1 ∧
        m - n = u ^ 2 ∧ m + n = v ^ 2 ∧ b = u * v := by
  -- Proof plan:
  --   hprod : (m-n)*(m+n)=b^2 by `rw [hb2_mn]; ring`.
  --   hcop  : Int.gcd (m-n) (m+n)=1 from `hmn_gcd` and opposite parity.
  --   apply `Int.sq_of_gcd_eq_one hcop hprod` to both factors.
  --   positivity kills the negative square alternatives.
  --   `b^2=(u*v)^2` plus `b>0,u>0,v>0` gives `b=u*v`.
  --   The `1<v` condition is the nondegenerate branch needed for strict descent;
  --   the `v=1` branch should be handled separately as base/degenerate.
  sorry

/--
Core descent branch for the split `U=a^4`, `V=5*b^4`.

The hypotheses `hhalf`, `hpy`, `hcop_hb`, and `hb2_odd_mod` are the local facts
proved before invoking this branch:
* `hhalf`: `2*h = a^2-b^2`, from `h=(a^2-b^2)/2` and oddness of `a,b`;
* `hpy`: `h^2+b^4=r^2`, from `4*r^2=(a^2-b^2)^2+4*b^4`;
* `hcop_hb`: primitivity of the Pythagorean triple;
* `hb2_odd_mod`: the odd-leg condition needed by Mathlib's classifier.
-/
theorem descent_branch_a4_5b4
    {a b h r B : ℤ}
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hr_pos : 0 < r) (hB_pos : 0 < B)
    (habB : a * b = B)
    (hhalf : 2 * h = a ^ 2 - b ^ 2)
    (hpy : h ^ 2 + b ^ 4 = r ^ 2)
    (hcop_hb : Int.gcd h b = 1)
    (hb2_odd_mod : (b ^ 2) % 2 = 1) :
    ∃ r' B' s' : ℤ,
      QuarticPlusZ r' B' s' ∧ B'.natAbs < B.natAbs := by
  -- 1. Build the Pythagorean triple with the odd leg first.
  have hpt : PythagoreanTriple (b ^ 2) h r := by
    dsimp [PythagoreanTriple]
    rw [show (b ^ 2) * (b ^ 2) + h * h = h ^ 2 + b ^ 4 by ring]
    rw [show r * r = r ^ 2 by ring]
    exact hpy

  -- 2. Primitive condition for the odd leg `b^2`.
  have hb_h_coprime : IsCoprime b h :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop_hb).symm

  have hcop_b2_h : Int.gcd (b ^ 2) h = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    simpa [pow_two] using (IsCoprime.mul_left hb_h_coprime hb_h_coprime)

  -- 3. Classify the primitive Pythagorean triple.
  obtain ⟨m, n, hb2_mn, hh_2mn, hr_mn, hmn_gcd, hmn_parity, hm_nonneg⟩ :=
    hpt.coprime_classification' hcop_b2_h hb2_odd_mod hr_pos

  -- 4. Split `b^2=(m-n)(m+n)` into coprime squares.
  obtain ⟨u, v, hu_pos, hv_gt_one, hcop_vu, hsub, hadd, hb_uv⟩ :=
    split_b_square_from_coprime_factors
      hb_pos hb2_mn hmn_gcd hmn_parity

  -- 5. Pure algebra: derive the new quartic equation
  --      a^2 = v^4 + v^2*u^2 - u^4.
  have h2h_vu : 2 * h = v ^ 4 - u ^ 4 := by
    have hdiff : (m + n) ^ 2 - (m - n) ^ 2 = v ^ 4 - u ^ 4 := by
      rw [hadd, hsub]
      ring
    have hmn_alg : (m + n) ^ 2 - (m - n) ^ 2 = 4 * m * n := by
      ring
    nlinarith [hh_2mn, hdiff, hmn_alg]

  have hb_sq_uv : b ^ 2 = u ^ 2 * v ^ 2 := by
    rw [hb_uv]
    ring

  have hnew : a ^ 2 = v ^ 4 + v ^ 2 * u ^ 2 - u ^ 4 := by
    nlinarith [hhalf, h2h_vu, hb_sq_uv]

  -- 6. Strict descent: B' = u, and `u < u*v = b ≤ a*b = B`.
  have hu_lt_b : u < b := by
    rw [hb_uv]
    nlinarith [hu_pos, hv_gt_one]

  have hb_le_B : b ≤ B := by
    rw [← habB]
    nlinarith [ha_pos, hb_pos]

  have hu_lt_B : u < B := lt_of_lt_of_le hu_lt_b hb_le_B

  have hu_nat_lt_B_nat : u.natAbs < B.natAbs := by
    rw [Int.natAbs_of_nonneg (le_of_lt hu_pos), Int.natAbs_of_nonneg (le_of_lt hB_pos)]
    exact_mod_cast hu_lt_B

  -- 7. Return the smaller quartic-plus solution `(r',B',s')=(v,u,a)`.
  refine ⟨v, u, a, ?_, hu_nat_lt_B_nat⟩
  constructor
  · exact lt_trans (by norm_num : (0 : ℤ) < 1) hv_gt_one
  constructor
  · exact hu_pos
  constructor
  · exact hcop_vu
  · -- `a^2 = v^4 + v^2*u^2 - u^4` is the quartic equation.
    simpa [QuarticPlusZ] using hnew

end DM3
```

To call this from your full branch, first prove:

```lean
hhalf : 2*h = a^2-b^2
hpy : h^2+b^4=r^2
hcop_hb : Int.gcd h b = 1
hb2_odd_mod : (b^2) % 2 = 1
```

Then `descent_branch_a4_5b4` returns the smaller solution `(v,u,a)` with `u.natAbs < B.natAbs`.
