# Q2427 Pythagorean API for EulerAux_param

Target local theorem:

```lean
def EulerAux (A D : ℤ) : Prop :=
  A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧ Nat.Coprime A.natAbs D.natAbs ∧
  ∃ S R : ℤ, S^2 = 4*A^2 + D^2 ∧ R^2 = 16*A^2 + D^2

theorem EulerAux_param {A D : ℤ} (hAD : EulerAux A D) :
  ∃ E P Q U V : ℤ,
    (E = D ∨ E = -D) ∧
    Even P ∧ Odd Q ∧ Even U ∧ Odd V ∧
    Nat.Coprime P.natAbs Q.natAbs ∧
    Nat.Coprime (2*U).natAbs V.natAbs ∧
    A = P*Q ∧ A = U*V ∧
    E = P^2 - Q^2 ∧ E = 4*U^2 - V^2
```

This drop is only about the primitive Pythagorean API and the route to `EulerAux_param`.

---

## 1. Import and Mathlib API

Use:

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Data.Int.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Tactic
```

The relevant Mathlib file is:

```text
Mathlib/NumberTheory/PythagoreanTriples.lean
```

Local search commands:

```bash
grep -n "def PythagoreanTriple" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
grep -n "coprime_classification" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
grep -n "theorem classification" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
grep -n "IsPrimitiveClassified" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
```

Expected declarations to check in Lean:

```lean
#check PythagoreanTriple
#check pythagoreanTriple_comm
#check PythagoreanTriple.symm
#check PythagoreanTriple.eq
#check PythagoreanTriple.mul
#check PythagoreanTriple.mul_iff
#check PythagoreanTriple.gcd_dvd
#check PythagoreanTriple.normalize
#check PythagoreanTriple.coprime_classification
#check PythagoreanTriple.coprime_classification'
#check PythagoreanTriple.classification
```

The important theorem is the primed classification.  Its current Mathlib shape is essentially:

```lean
theorem PythagoreanTriple.coprime_classification'
    {x y z : ℤ}
    (h : PythagoreanTriple x y z)
    (h_coprime : Int.gcd x y = 1)
    (h_parity : x % 2 = 1)
    (h_pos : 0 < z) :
    ∃ m n,
      x = m ^ 2 - n ^ 2 ∧
      y = 2 * m * n ∧
      z = m ^ 2 + n ^ 2 ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      0 ≤ m
```

There is also an unprimed primitive classification without choosing the odd leg:

```lean
#check PythagoreanTriple.coprime_classification
```

Expected shape:

```lean
PythagoreanTriple x y z ∧ Int.gcd x y = 1 ↔
  ∃ m n,
    (x = m^2 - n^2 ∧ y = 2*m*n ∨
     x = 2*m*n ∧ y = m^2 - n^2) ∧
    (z = m^2+n^2 ∨ z = -(m^2+n^2)) ∧
    Int.gcd m n = 1 ∧
    (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
```

For `EulerAux_param`, prefer `coprime_classification'` by feeding the **odd leg first**:

```text
first triangle:  x = D, y = 2*A, z = |S|
second triangle: x = D, y = 4*A, z = |R|.
```

This avoids the branch where Mathlib swaps the odd/even legs.

---

## 2. Basic local definitions

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Data.Int.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace FLT.Mazur.N12.EulerAuxParam

noncomputable section

def EulerAux (A D : ℤ) : Prop :=
  A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧ Nat.Coprime A.natAbs D.natAbs ∧
  ∃ S R : ℤ, S^2 = 4*A^2 + D^2 ∧ R^2 = 16*A^2 + D^2

/-- The sign-normalized odd leg: the unique one of `D`, `-D` congruent to `-1 mod 4`. -/
def normOddLeg (D : ℤ) : ℤ :=
  if D % 4 = 3 then D else -D
```

In Lean, use `E % 4 = 3` for `E ≡ -1 mod 4`, because `Int.emod` has nonnegative remainder.

---

## 3. Nat-vs-Int conversion lemmas

Mathlib's Pythagorean classification uses `Int.gcd x y = 1`, while `EulerAux` uses

```lean
Nat.Coprime A.natAbs D.natAbs
```

Add these local bridge lemmas first.

```lean
/-- Convert Mathlib's `Int.gcd` form to the `natAbs` coprime form. -/
theorem natAbs_coprime_of_int_gcd_eq_one {a b : ℤ}
    (h : Int.gcd a b = 1) :
    Nat.Coprime a.natAbs b.natAbs := by
  -- `Int.gcd a b` is definitionally `Nat.gcd a.natAbs b.natAbs`.
  -- Search/check:
  --   #check Int.gcd_def
  --   #check Nat.coprime_iff_gcd_eq_one
  -- Expected proof:
  --   rw [Nat.coprime_iff_gcd_eq_one]
  --   simpa [Int.gcd] using h
  sorry

/-- Convert `natAbs` coprime form to Mathlib's `Int.gcd = 1` form. -/
theorem int_gcd_eq_one_of_natAbs_coprime {a b : ℤ}
    (h : Nat.Coprime a.natAbs b.natAbs) :
    Int.gcd a b = 1 := by
  -- Expected proof:
  --   rw [Nat.coprime_iff_gcd_eq_one] at h
  --   simpa [Int.gcd] using h
  sorry

/-- `D` odd and coprime to `A` implies `D` coprime to `2*A`. -/
theorem int_gcd_D_twoA_eq_one
    {A D : ℤ}
    (hOddD : Odd D)
    (hcop : Nat.Coprime A.natAbs D.natAbs) :
    Int.gcd D (2*A) = 1 := by
  -- Proof plan:
  -- 1. Prove `Nat.Coprime (2 : ℕ) D.natAbs` from `Odd D`.
  --    Search:
  --      #check Nat.coprime_two_right
  --      #check Nat.Prime.coprime_iff_not_dvd
  --      #check Int.odd_iff_not_even
  --      #check Int.dvd_natAbs
  -- 2. Rewrite `(2*A).natAbs = 2 * A.natAbs`.
  --    Search:
  --      #check Int.natAbs_mul
  -- 3. Use `Nat.Coprime.mul_left`/`mul_right` or the equivalent theorem.
  --    Search:
  --      #check Nat.Coprime.mul_left
  --      #check Nat.Coprime.mul_right
  --      #check Nat.coprime_mul_left_iff
  --      #check Nat.coprime_mul_right_iff
  -- 4. Convert back with `int_gcd_eq_one_of_natAbs_coprime`.
  sorry

/-- Same coprimality for the second triangle. -/
theorem int_gcd_D_fourA_eq_one
    {A D : ℤ}
    (hOddD : Odd D)
    (hcop : Nat.Coprime A.natAbs D.natAbs) :
    Int.gcd D (4*A) = 1 := by
  -- Same proof as `int_gcd_D_twoA_eq_one`, using `4 = 2*2` and oddness of `D`.
  sorry
```

These are not mathematically hard; they are API/cast lemmas.

---

## 4. Sign normalization lemmas

The parametrization should return the same sign from both triangles.  The clean way is to normalize the odd leg to be `≡ -1 mod 4`.

```lean
/-- `normOddLeg D` is one of `D` and `-D`. -/
theorem normOddLeg_eq_or_eq_neg (D : ℤ) :
    normOddLeg D = D ∨ normOddLeg D = -D := by
  unfold normOddLeg
  by_cases h : D % 4 = 3 <;> simp [h]

/-- For odd `D`, `normOddLeg D ≡ -1 mod 4`. -/
theorem normOddLeg_mod_four {D : ℤ} (hOddD : Odd D) :
    normOddLeg D % 4 = 3 := by
  -- Proof plan:
  -- 1. Convert `Odd D` to `D % 2 = 1`.
  --    Search:
  --      #check Int.odd_iff
  --      #check Int.not_even_iff_odd
  -- 2. Show `D % 4 = 1 ∨ D % 4 = 3`, e.g. by `omega` from
  --    `0 ≤ D % 4`, `D % 4 < 4`, and compatibility mod 2.
  -- 3. If `D % 4 = 3`, simplify `normOddLeg`.
  -- 4. If `D % 4 = 1`, simplify `normOddLeg = -D` and prove `(-D) % 4 = 3`.
  sorry

/-- If an odd-leg representation has even parameter first, it uses the normalized sign. -/
theorem normOddLeg_eq_of_even_odd_sq_sub
    {D P Q : ℤ}
    (hD : D = P^2 - Q^2)
    (hP : Even P) (hQ : Odd Q) :
    normOddLeg D = D := by
  -- Because `P² ≡ 0 mod 4` and `Q² ≡ 1 mod 4`, so `D % 4 = 3`.
  -- `omega`/`norm_num` after unpacking parity is usually enough.
  sorry

/-- If an odd-leg representation has odd parameter first, swapping gives the normalized sign. -/
theorem normOddLeg_eq_neg_of_odd_even_sq_sub
    {D P Q : ℤ}
    (hD : D = P^2 - Q^2)
    (hP : Odd P) (hQ : Even Q) :
    normOddLeg D = -D := by
  -- Because `D % 4 = 1`, so normalized leg is `-D`.
  sorry
```

These are pure parity/mod-4 lemmas.

---

## 5. Convert squared equations to Pythagorean triples

The classification theorem expects `PythagoreanTriple x y z`, i.e. `x*x + y*y = z*z`, and a positive hypotenuse.  Use `natAbs` of the supplied square root.

```lean
/-- Use the nonnegative integer `S.natAbs` as the positive hypotenuse. -/
abbrev absInt (S : ℤ) : ℤ := (S.natAbs : ℤ)

theorem absInt_sq (S : ℤ) :
    (absInt S)^2 = S^2 := by
  -- `norm_num [absInt]` may close; otherwise use `Int.natAbs_sq`/`sq_abs` search.
  -- Search:
  --   #check Int.natAbs_mul_self
  --   #check Int.natAbs_sq
  sorry

theorem absInt_pos_of_sq_rhs_pos
    {S rhs : ℤ} (hS : S^2 = rhs) (hrhs : 0 < rhs) :
    0 < absInt S := by
  -- From `hrhs`, get `S ≠ 0`; then `0 < S.natAbs`.
  sorry

theorem pythagoreanTriple_D_twoA_absS
    {A D S : ℤ}
    (hS : S^2 = 4*A^2 + D^2) :
    PythagoreanTriple D (2*A) (absInt S) := by
  unfold PythagoreanTriple absInt
  -- Use `absInt_sq S` and ring/nlinarith.
  have hsabs : ((S.natAbs : ℤ))^2 = S^2 := by
    -- call `absInt_sq S`
    simpa [absInt] using absInt_sq S
  nlinarith [hS, hsabs]

theorem pythagoreanTriple_D_fourA_absR
    {A D R : ℤ}
    (hR : R^2 = 16*A^2 + D^2) :
    PythagoreanTriple D (4*A) (absInt R) := by
  unfold PythagoreanTriple absInt
  have hrabs : ((R.natAbs : ℤ))^2 = R^2 := by
    simpa [absInt] using absInt_sq R
  nlinarith [hR, hrabs]
```

---

## 6. First parametrization: `S² = 4A² + D²`

This is the first small theorem to prove before `EulerAux_param`.

```lean
/-- Primitive parametrization of the first triangle

```text
D² + (2A)² = S².
```

It yields `A=P*Q` and the normalized odd leg `E=P²-Q²`, with `P` even and `Q` odd.
-/
theorem twoA_triangle_param
    {A D S : ℤ}
    (hDne : D ≠ 0)
    (hOddD : Odd D)
    (hcop : Nat.Coprime A.natAbs D.natAbs)
    (hS : S^2 = 4*A^2 + D^2) :
    ∃ P Q : ℤ,
      Even P ∧ Odd Q ∧
      Nat.Coprime P.natAbs Q.natAbs ∧
      A = P*Q ∧
      normOddLeg D = P^2 - Q^2 := by
  -- Route:
  -- 1. `hpy := pythagoreanTriple_D_twoA_absS hS`.
  -- 2. `hgcd := int_gcd_D_twoA_eq_one hOddD hcop`.
  -- 3. `hpar : D % 2 = 1` from `Odd D`.
  -- 4. `hpos : 0 < absInt S` because `D ≠ 0` implies `0 < 4*A² + D²`.
  -- 5. Apply:
  --      rcases PythagoreanTriple.coprime_classification'
  --        hpy hgcd hpar hpos with ⟨m,n,hD,h2A,hHyp,hg,hparmn,hmnonneg⟩
  -- 6. Cancel `2` in `h2A : 2*A = 2*m*n` to get `A=m*n`.
  -- 7. Branch on `hparmn`:
  --    * `m even`, `n odd`: set `P=m`, `Q=n`; `normOddLeg D = D` by mod-4.
  --    * `m odd`, `n even`: set `P=n`, `Q=m`; `normOddLeg D = -D`; then
  --      `-D = n²-m²` by `hD`.
  -- 8. Convert `Int.gcd m n = 1` to `Nat.Coprime m.natAbs n.natAbs`.
  sorry
```

Notes:

* `D` is allowed to be negative.  The classification theorem only needs `D % 2 = 1`, which holds for odd negative integers too under `Int.emod`.
* The sign in the final theorem is handled by `normOddLeg`; do not try to force `D=P²-Q²` directly.

---

## 7. Second parametrization: `R² = 16A² + D²`

This is the second small theorem to prove.  It uses `Even A`, which will be obtained from the first parametrization (`A=P*Q`, `Even P`).

```lean
/-- Primitive parametrization of the second triangle

```text
D² + (4A)² = R².
```

With `A` even, the normalized odd leg has the form `4U² - V²`, with
`U` even and `V` odd.
-/
theorem fourA_triangle_param
    {A D R : ℤ}
    (hAeven : Even A)
    (hDne : D ≠ 0)
    (hOddD : Odd D)
    (hcop : Nat.Coprime A.natAbs D.natAbs)
    (hR : R^2 = 16*A^2 + D^2) :
    ∃ U V : ℤ,
      Even U ∧ Odd V ∧
      Nat.Coprime (2*U).natAbs V.natAbs ∧
      A = U*V ∧
      normOddLeg D = 4*U^2 - V^2 := by
  -- Route:
  -- 1. `hpy := pythagoreanTriple_D_fourA_absR hR`.
  -- 2. `hgcd := int_gcd_D_fourA_eq_one hOddD hcop`.
  -- 3. `hpar : D % 2 = 1` from `Odd D`.
  -- 4. `hpos : 0 < absInt R` because `D ≠ 0`.
  -- 5. Apply `PythagoreanTriple.coprime_classification'` to `(D, 4*A, absInt R)`:
  --      D = m²-n²,
  --      4*A = 2*m*n,
  --      Int.gcd m n = 1,
  --      opposite parity.
  -- 6. Cancel `2` to get `2*A = m*n`.
  -- 7. Branch on parity:
  --    * `m even`, `n odd`:
  --        write `m = 2*U`, set `V=n`.
  --        Then `2*A = 2*U*V`, so `A=U*V`.
  --        `D = 4U² - V²`, hence `normOddLeg D = D`.
  --    * `m odd`, `n even`:
  --        write `n = 2*U`, set `V=m`.
  --        Then `2*A = 2*U*V`, so `A=U*V`.
  --        `D = V² - 4U²`, hence `normOddLeg D = -D = 4U² - V²`.
  -- 8. Prove `Even U` from `A=U*V`, `Even A`, and `Odd V`.
  --    Local lemma to add:
  --      theorem even_left_of_even_mul_odd {u v : ℤ} : Even (u*v) → Odd v → Even u
  -- 9. The gcd field is exactly Mathlib's `Int.gcd m n = 1`, rewritten after
  --    `m=2U` or `n=2U` to `Nat.Coprime (2*U).natAbs V.natAbs`.
  sorry
```

The `Even U` requirement is **not** a direct output of the second Pythagorean classification.  It uses the first triangle indirectly via `Even A`.

Useful local lemma:

```lean
theorem even_left_of_even_mul_odd {u v : ℤ}
    (huv : Even (u*v)) (hv : Odd v) : Even u := by
  -- Proof options:
  -- * use parity cases on `u`, `v`;
  -- * or use `Int.even_iff`, `Int.odd_iff_not_even`, and divisibility.
  -- Search:
  --   #check Even.mul_left
  --   #check Even.mul_right
  --   #check Odd.mul
  --   #check Int.even_mul
  --   #check Int.odd_iff_not_even
  sorry
```

---

## 8. Final assembly theorem

Once `twoA_triangle_param` and `fourA_triangle_param` are proved, the final theorem is mostly unpacking.

```lean
theorem EulerAux_param {A D : ℤ} (hAD : EulerAux A D) :
  ∃ E P Q U V : ℤ,
    (E = D ∨ E = -D) ∧
    Even P ∧ Odd Q ∧ Even U ∧ Odd V ∧
    Nat.Coprime P.natAbs Q.natAbs ∧
    Nat.Coprime (2*U).natAbs V.natAbs ∧
    A = P*Q ∧ A = U*V ∧
    E = P^2 - Q^2 ∧ E = 4*U^2 - V^2 := by
  rcases hAD with ⟨hAne, hDne, hOddD, hcop, S, R, hS, hR⟩

  rcases twoA_triangle_param hDne hOddD hcop hS with
    ⟨P, Q, hPeven, hQodd, hPQcop, hA_PQ, hE_PQ⟩

  have hAeven : Even A := by
    -- from `A = P*Q` and `Even P`
    rw [hA_PQ]
    exact hPeven.mul_right Q

  rcases fourA_triangle_param hAeven hDne hOddD hcop hR with
    ⟨U, V, hUeven, hVodd, hUVcop, hA_UV, hE_UV⟩

  refine ⟨normOddLeg D, P, Q, U, V, normOddLeg_eq_or_eq_neg D,
    hPeven, hQodd, hUeven, hVodd, hPQcop, hUVcop,
    hA_PQ, hA_UV, hE_PQ, hE_UV⟩
```

This final proof should compile once the helper theorem statements are implemented.

---

## 9. Why `E = D ∨ E = -D` and `E ≡ -1 mod 4` are the right Lean normalization

For a primitive Pythagorean triple with odd leg first,

```text
D = m² - n²,
2A = 2mn,
```

Mathlib returns opposite parity:

```text
m even, n odd    or    m odd, n even.
```

But the desired output always wants the even parameter first:

```text
P even, Q odd, E = P² - Q².
```

So:

* if `m` is even and `n` is odd, set `P=m`, `Q=n`, and `E=D`;
* if `m` is odd and `n` is even, set `P=n`, `Q=m`, and `E=-D`.

In both cases,

```text
E = P² - Q² ≡ -1 mod 4.
```

The second triangle has the same normalized sign:

```text
E = 4U² - V² ≡ -1 mod 4.
```

Thus defining

```lean
def normOddLeg (D : ℤ) : ℤ := if D % 4 = 3 then D else -D
```

avoids a later proof that two independently chosen signs agree.

---

## 10. Minimal implementation checklist

Implement in this order:

```lean
-- gcd/parity bridges
natAbs_coprime_of_int_gcd_eq_one
int_gcd_eq_one_of_natAbs_coprime
int_gcd_D_twoA_eq_one
int_gcd_D_fourA_eq_one

-- sign normalization
normOddLeg
normOddLeg_eq_or_eq_neg
normOddLeg_mod_four
normOddLeg_eq_of_even_odd_sq_sub
normOddLeg_eq_neg_of_odd_even_sq_sub

-- absolute hypotenuse conversion
absInt
absInt_sq
absInt_pos_of_sq_rhs_pos
pythagoreanTriple_D_twoA_absS
pythagoreanTriple_D_fourA_absR

-- special primitive parametrizations
twoA_triangle_param
fourA_triangle_param

-- final assembly
EulerAux_param
```

No part of this route requires full-cover/AP normalization or elliptic-curve input.  The only external mathematical ingredient is Mathlib's primitive Pythagorean triple classification.

```lean
end
end FLT.Mazur.N12.EulerAuxParam
```
