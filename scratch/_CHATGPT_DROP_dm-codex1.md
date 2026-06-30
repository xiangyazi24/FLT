# Q2432-RETRY gcd lemma truth audit

Scope: this audits only Lemma A and Lemma B from Q2432-RETRY.  I am not giving an EulerAux descent DAG here.

## Verdicts

### Lemma A

`two_coprime_factorizations_refine_even` is true as stated, assuming

```lean
def PairwiseCoprime2abcd (a b c d : ℤ) : Prop :=
  Nat.Coprime (2*a).natAbs b.natAbs ∧
  Nat.Coprime (2*a).natAbs c.natAbs ∧
  Nat.Coprime (2*a).natAbs d.natAbs ∧
  Nat.Coprime b.natAbs c.natAbs ∧
  Nat.Coprime b.natAbs d.natAbs ∧
  Nat.Coprime c.natAbs d.natAbs
```

No positivity/sign-normalization hypotheses are needed for the stated existential theorem.  The proof should be done by first proving a nonnegative/natAbs grid-refinement theorem and then re-inserting signs.  A useful strengthening is to also return `Odd b ∧ Odd c ∧ Odd d`; the user statement only asks for `Odd d`.

The hypothesis `hA : A ≠ 0` is necessary.  If it is removed, `A = 0, P = 0, Q = 1, U = 0, V = 1` satisfies the parity and coprimality hypotheses but cannot satisfy the requested nonzero conclusions for `a,b,c,d`.

### Lemma B

`square_factor_balance` is true as stated.

The positivity assumptions on `M,N` are essential for this exact signed conclusion.  If they are replaced by mere nonzero hypotheses, then

```text
b = 2, c = 3, M = -9, N = -4
```

satisfies `b^2*M = c^2*N`, the two coprimality hypotheses, and `M,N ≠ 0`, but the conclusion `M = c^2 ∧ N = b^2` is false.  With the stated `0 < M` and `0 < N`, there is no counterexample.

---

## Lemma A: Lean-friendly proof DAG

Recommended imports for a standalone scratch proof:

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.Parity
import Mathlib.Data.Nat.GCD.Basic
```

If the surrounding file already imports `Mathlib`, no extra imports are needed.

### Step A1: reduce to natural absolute values

From

```lean
hPQ : A = P*Q
hUV : A = U*V
hA  : A ≠ 0
```

first prove

```lean
have hP0 : P ≠ 0 := by
  intro hP
  apply hA
  rw [hPQ, hP, zero_mul]

have hQ0 : Q ≠ 0 := by
  intro hQ
  apply hA
  rw [hPQ, hQ, mul_zero]

have hU0 : U ≠ 0 := by
  intro hU
  apply hA
  rw [hUV, hU, zero_mul]

have hV0 : V ≠ 0 := by
  intro hV
  apply hA
  rw [hUV, hV, mul_zero]
```

Then set

```lean
let p : ℕ := P.natAbs
let q : ℕ := Q.natAbs
let u : ℕ := U.natAbs
let v : ℕ := V.natAbs
```

and derive

```lean
p * q = u * v
Nat.Coprime p q
Nat.Coprime u v
Even p
Even u
Odd q
Odd v
p ≠ 0
q ≠ 0
u ≠ 0
v ≠ 0
```

Key APIs/cast lemmas:

```lean
Int.natAbs_mul
Int.natAbs_pow
Int.natAbs_eq_zero
```

For the parity casts, I would prove two local lemmas once rather than fighting simp search:

```lean
lemma even_natAbs_of_even_int {n : ℤ} (h : Even n) : Even n.natAbs := by
  rcases h with ⟨k, hk⟩
  rw [hk]
  -- normalize `k + k` to `2*k`, then use `Int.natAbs_mul`
  refine ⟨k.natAbs, ?_⟩
  rw [show k + k = 2*k by ring]
  simp [Int.natAbs_mul]

lemma odd_natAbs_of_odd_int {n : ℤ} (h : Odd n) : Odd n.natAbs := by
  -- If the local Mathlib branch has a simp theorem for `Odd n.natAbs`, use it.
  -- Otherwise prove by cases on `Int.natAbs_eq n` or by reducing `n = ± n.natAbs`.
  -- The statement is true and should be kept as a small local parity bridge.
  sorry
```

The second lemma is deliberately separated because negative odd integers are the only nuisance; once proved, it is reused in every descent-normalization file.

### Step A2: prove a Nat grid refinement theorem

Prove this Nat theorem first:

```lean
theorem nat_two_coprime_factorizations_refine_even
    {p q u v : ℕ}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hprod : p*q = u*v)
    (hp_even : Even p) (hu_even : Even u)
    (hq_odd : Odd q) (hv_odd : Odd v)
    (hcopPQ : Nat.Coprime p q)
    (hcopUV : Nat.Coprime u v) :
    ∃ a b c d : ℕ,
      p = 2*a*b ∧ q = c*d ∧ u = 2*a*c ∧ v = b*d ∧
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
      Odd b ∧ Odd c ∧ Odd d ∧
      Nat.Coprime (2*a) b ∧
      Nat.Coprime (2*a) c ∧
      Nat.Coprime (2*a) d ∧
      Nat.Coprime b c ∧
      Nat.Coprime b d ∧
      Nat.Coprime c d
```

Proof outline for the Nat theorem:

1. Let `g := Nat.gcd p u`.
2. Use `Nat.gcd_dvd_left` and `Nat.gcd_dvd_right` to write

   ```lean
   p = g*b
   u = g*c
   ```

3. Use `Even p`, `Even u` to prove `2 ∣ g`; write `g = 2*a`.

   Key API:

   ```lean
   Nat.dvd_gcd
   ```

4. Since `g ≠ 0`, cancel `g` in `g*b*q = g*c*v` to get

   ```lean
   b*q = c*v
   ```

   Key API:

   ```lean
   mul_left_cancel₀
   ring_nf
   ```

5. Prove `Nat.Coprime b c`.  There are two viable routes:

   * use the standard division-by-gcd lemma if available in the local branch, usually searchable as `Nat.coprime_div_gcd_div_gcd`; or
   * prove it directly: if a number divides both `b` and `c`, then after multiplying by `g` it divides both `p` and `u`, hence it divides `g`, and then cancellation against the quotient equations forces it to be `1`.

6. From `b*q = c*v` and `Nat.Coprime b c`, get `c ∣ q`.

   Use the current Mathlib Euclid API in this shape:

   ```lean
   have hc_dvd_q : c ∣ q := by
     -- from `c ∣ b*q` and `Nat.Coprime c b`
     exact (hcb.dvd_mul_left).mp ?_
   ```

   In current Mathlib, the relevant theorems are:

   ```lean
   Nat.Coprime.dvd_mul_left
   Nat.Coprime.dvd_mul_right
   -- underlying methods also appear as:
   h.dvd_of_dvd_mul_left
   h.dvd_of_dvd_mul_right
   ```

7. Choose `d` with `q = c*d`; substitute into `b*q = c*v`; cancel nonzero `c` to get `v = b*d`.

8. Nonzero conclusions follow from nonzero `p,q,u,v` and the product equations.

9. Oddness:

   Since `q = c*d` and `q` is odd, both `c` and `d` are odd.  Since `v = b*d` and `v` is odd, `b` is odd.

10. Pairwise coprimality:

   Use divisibility into the original coprime pairs.  The most useful current Mathlib APIs are:

   ```lean
   Nat.Coprime.of_dvd_left
   Nat.Coprime.of_dvd_right
   Nat.Coprime.of_dvd
   ```

   For example:

   * `Nat.Coprime (2*a) c`: `2*a ∣ p` and `c ∣ q`, then use `hcopPQ.of_dvd`.
   * `Nat.Coprime (2*a) b`: `2*a ∣ u` and `b ∣ v`, then use `hcopUV.of_dvd`.
   * `Nat.Coprime (2*a) d`: use `2*a ∣ p` and `d ∣ q`, then `hcopPQ.of_dvd`.
   * `Nat.Coprime b c`: already proved above.
   * `Nat.Coprime b d`: use `b ∣ p` and `d ∣ q`, then `hcopPQ.of_dvd`.
   * `Nat.Coprime c d`: use `c ∣ u` and `d ∣ v`, then `hcopUV.of_dvd`.

This Nat theorem is the main content of Lemma A.  It avoids all sign issues.

### Step A3: reinsert signs over `ℤ`

After Step A2 gives natural `a0 b0 c0 d0` satisfying the natAbs equations, choose signed integers as follows.

Keep `a` positive:

```lean
let a : ℤ := a0
```

Choose `b` to match `P = 2*a*b`:

```lean
let b : ℤ := if P < 0 then -(b0 : ℤ) else (b0 : ℤ)
```

Choose `c` to match `U = 2*a*c`:

```lean
let c : ℤ := if U < 0 then -(c0 : ℤ) else (c0 : ℤ)
```

Then obtain `d` from the divisibility `c ∣ Q`, equivalently from the absolute equation `Q.natAbs = c0*d0` and the sign choice for `c`:

```lean
obtain ⟨d, hQcd : Q = c*d⟩ : ∃ d : ℤ, Q = c*d := by
  -- use `Q.natAbs = c0*d0` and the chosen sign of `c`
  -- or define `d` explicitly by signs.
  sorry
```

Now prove `V = b*d` by cancellation from the original equality:

```lean
have hprod_int : P*Q = U*V := by
  rw [← hPQ, hUV]

-- after substituting `P = 2*a*b`, `U = 2*a*c`, `Q = c*d`:
-- `(2*a*b)*(c*d) = (2*a*c)*V`
-- normalize to `(2*a*c)*(b*d) = (2*a*c)*V`
-- cancel `2*a*c ≠ 0`
```

Key APIs:

```lean
ring_nf
mul_left_cancel₀
```

This route is better than trying to solve all four sign equations simultaneously.  It only chooses signs for `b,c`; the sign of `d` is forced by `Q = c*d`, and `V = b*d` follows from `P*Q = U*V`.

### Lemma A sign conclusion

No positivity assumptions on `P,Q,U,V,A` are required.  The existential signs can always be chosen.  The only sign-sensitive facts needed are:

```lean
P ≠ 0, Q ≠ 0, U ≠ 0, V ≠ 0
```

which follow from `hA`, `hPQ`, and `hUV`.

---

## Lemma B: Lean-friendly proof DAG

The cleanest implementation is to prove the natural-number theorem first and then transport from `ℤ` using `natAbs` and the positivity of `M,N`.

### Step B1: Nat helper

```lean
theorem nat_square_factor_balance
    {B C M N : ℕ}
    (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : Nat.Coprime B C)
    (hMN : Nat.Coprime M N)
    (h : B^2 * M = C^2 * N) :
    M = C^2 ∧ N = B^2 := by
  -- 1. Coprime squares.
  have hB2C2 : Nat.Coprime (B^2) (C^2) := by
    exact (hBC.pow_left 2).pow_right 2
  have hC2B2 : Nat.Coprime (C^2) (B^2) := hB2C2.symm

  -- 2. C^2 divides M because C^2 divides B^2*M and is coprime to B^2.
  have hC2_dvd_M : C^2 ∣ M := by
    have hdiv : C^2 ∣ B^2 * M := by
      rw [h]
      exact dvd_mul_right (C^2) N
    exact (hC2B2.dvd_mul_left).mp hdiv

  -- 3. B^2 divides N because B^2 divides C^2*N and is coprime to C^2.
  have hB2_dvd_N : B^2 ∣ N := by
    have hdiv : B^2 ∣ C^2 * N := by
      rw [← h]
      exact dvd_mul_right (B^2) M
    exact (hB2C2.dvd_mul_left).mp hdiv

  rcases hC2_dvd_M with ⟨t, hM⟩
  rcases hB2_dvd_N with ⟨s, hN⟩

  -- 4. Substitute and cancel the common nonzero factor B^2*C^2.
  have hts : t = s := by
    have hcommon : (B^2 * C^2) * t = (B^2 * C^2) * s := by
      -- `h`, `hM`, `hN`, then commutative semiring normalization.
      rw [hM, hN] at h
      ring_nf at h ⊢
      exact h
    have hcommon0 : B^2 * C^2 ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero 2 hB) (pow_ne_zero 2 hC)
    exact mul_left_cancel₀ hcommon0 hcommon

  subst s

  -- 5. The common multiplier t divides both M and N; coprimality forces t=1.
  have ht_dvd_M : t ∣ M := by
    rw [hM]
    exact dvd_mul_left t (C^2)
  have ht_dvd_N : t ∣ N := by
    rw [hN]
    exact dvd_mul_left t (B^2)
  have ht1 : t = 1 := Nat.eq_one_of_dvd_coprimes hMN ht_dvd_M ht_dvd_N

  constructor
  · rw [hM, ht1, mul_one]
  · rw [hN, ht1, mul_one]
```

The theorem names above are the important current Mathlib APIs:

```lean
Nat.Coprime.pow_left
Nat.Coprime.pow_right
Nat.Coprime.dvd_mul_left
Nat.Coprime.dvd_mul_right
Nat.eq_one_of_dvd_coprimes
mul_left_cancel₀
pow_ne_zero
```

If the local simplifier does not like the `ring_nf` block after rewriting `hM,hN`, replace it with an explicit associativity/commutativity normalization using `ac_rfl`-style rewrites.  The mathematical cancellation target is simply

```lean
(B^2 * C^2) * t = (B^2 * C^2) * s
```

### Step B2: Int theorem from the Nat helper

For the stated integer theorem, set

```lean
let B : ℕ := b.natAbs
let C : ℕ := c.natAbs
let MM : ℕ := M.natAbs
let NN : ℕ := N.natAbs
```

From `h : b^2 * M = c^2 * N`, prove the Nat equality

```lean
B^2 * MM = C^2 * NN
```

by applying `congrArg Int.natAbs h` and simplifying with

```lean
Int.natAbs_mul
Int.natAbs_pow
```

The positivity hypotheses convert `MM,NN` back to `M,N` without ambiguity:

```lean
have hM_nonneg : 0 ≤ M := le_of_lt hMpos
have hN_nonneg : 0 ≤ N := le_of_lt hNpos
```

Then use the local cast/simp facts

```lean
((M.natAbs : ℕ) : ℤ) = M
((N.natAbs : ℕ) : ℤ) = N
((b.natAbs ^ 2 : ℕ) : ℤ) = b^2
((c.natAbs ^ 2 : ℕ) : ℤ) = c^2
```

The first two are via `Int.natAbs_of_nonneg`; the square casts are via `Int.natAbs_pow` plus norm-cast/simp.

Skeleton:

```lean
theorem square_factor_balance
    {b c M N : ℤ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hMpos : 0 < M) (hNpos : 0 < N)
    (hbc : Nat.Coprime b.natAbs c.natAbs)
    (hMN : Nat.Coprime M.natAbs N.natAbs)
    (h : b^2 * M = c^2 * N) :
    M = c^2 ∧ N = b^2 := by
  let B : ℕ := b.natAbs
  let C : ℕ := c.natAbs
  let MM : ℕ := M.natAbs
  let NN : ℕ := N.natAbs

  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact mt Int.natAbs_eq_zero.mp hb
  have hC0 : C ≠ 0 := by
    dsimp [C]
    exact mt Int.natAbs_eq_zero.mp hc

  have hnat : B^2 * MM = C^2 * NN := by
    -- `congrArg Int.natAbs h`, then simp [B,C,MM,NN, Int.natAbs_mul, Int.natAbs_pow]
    sorry

  have hnat_bal := nat_square_factor_balance hB0 hC0 hbc hMN hnat
  rcases hnat_bal with ⟨hMM, hNN⟩

  constructor
  · -- cast `hMM : MM = C^2` back to integers using `0 < M`
    -- result: `M = c^2`
    sorry
  · -- cast `hNN : NN = B^2` back to integers using `0 < N`
    -- result: `N = b^2`
    sorry
```

This is the smallest robust proof shape.  The real content is the Nat helper; the integer theorem is only a `natAbs` transport plus positivity casts.

---

## Corrected/strengthened statements

No correction is needed for either lemma.

For Lemma A, I recommend proving the following stronger theorem internally and deriving the user statement by projection:

```lean
theorem two_coprime_factorizations_refine_even_strong
    {A P Q U V : ℤ}
    (hPQ : A = P*Q) (hUV : A = U*V)
    (hP_even : Even P) (hU_even : Even U)
    (hQ_odd : Odd Q) (hV_odd : Odd V)
    (hcopPQ : Nat.Coprime P.natAbs Q.natAbs)
    (hcopUV : Nat.Coprime U.natAbs V.natAbs)
    (hA : A ≠ 0) :
    ∃ a b c d : ℤ,
      P = 2*a*b ∧ Q = c*d ∧ U = 2*a*c ∧ V = b*d ∧
      A = 2*a*b*c*d ∧
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
      Odd b ∧ Odd c ∧ Odd d ∧
      PairwiseCoprime2abcd a b c d
```

The original Lemma A follows immediately by dropping `Odd b` and `Odd c`.

For Lemma B, keep the statement exactly as proposed.  Do not weaken `0 < M` and `0 < N` unless you change the conclusion to a signed alternative such as `M = c^2 ∧ N = b^2` for the positive case and `M = -c^2 ∧ N = -b^2` for the negative case.
