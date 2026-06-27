# Q1156 (dm2): concrete A-Line order-divisor reduction in Lean 4

## Main correction

The theorem as stated

```text
if E has a rational point of order n >= 17,
then E has a rational point of prime order p with p >= 11
```

is **false** as a pure order-divisor statement.

Example at the group-theory level: a cyclic group of order `18` has an element of order `18`, but its prime-order elements have orders only `2` and `3`.  So a point of order `18` would not imply a point of prime order `>= 11`.

For elliptic curves over `Q`, order `18` is indeed impossible, but that is a **composite-order exclusion**, not a consequence of prime divisors.  Therefore the correct reduction theorem is one of these two forms:

```text
point of order n >= 17
  -> either point of prime order p >= 11
     or point of one of the critical composite orders
```

or, after assuming all critical composite exclusions:

```text
point of order n >= 17
  -> point of prime order p >= 11.
```

This is the clean Lean split.

---

## The key group-theory lemma

The core lemma is independent of elliptic curves:

```text
if P has exact additive order n and d | n, then (n / d) • P has exact order d.
```

For the prime case, take `d = p`.

The Mathlib theorem this should use is the additive version of `orderOf_pow`, usually named:

```lean
addOrderOf_nsmul
```

with statement morally:

```lean
addOrderOf (k • P) = addOrderOf P / Nat.gcd (addOrderOf P) k
```

Here is the concrete Lean shape.

```lean
import Mathlib

namespace FLT

open scoped BigOperators

/--
Pure group theory: if `P` has exact additive order `n`, and `d` is a positive
divisor of `n`, then `(n / d) • P` has exact additive order `d`.

This is the divisor-of-order lemma needed for elliptic-curve torsion reductions.
-/
lemma addOrderOf_nsmul_div_eq_of_dvd
    {G : Type*} [AddGroup G] {P : G} {n d : ℕ}
    (hP : addOrderOf P = n)
    (hnpos : 0 < n)
    (hdpos : 0 < d)
    (hd : d ∣ n) :
    addOrderOf ((n / d) • P) = d := by
  have hle : d ≤ n := Nat.le_of_dvd hnpos hd
  have hkpos : 0 < n / d := Nat.div_pos hle hdpos
  have hquot : n / (n / d) = d := by
    -- Since `d ∣ n`, write `n = (n / d) * d` and divide by `n / d`.
    have hmul : n = (n / d) * d := (Nat.div_mul_cancel hd).symm
    rw [hmul]
    -- The theorem name below is stable in current Mathlib-style Nat API.
    -- If local Mathlib spells it differently, search for `Nat.mul_div_right` or
    -- `Nat.mul_div_cancel_left`.
    rw [Nat.mul_comm]
    exact Nat.mul_div_right d hkpos
  have hgcd : Nat.gcd n (n / d) = n / d := by
    have hdiv : n / d ∣ n := ⟨d, (Nat.div_mul_cancel hd).symm⟩
    exact Nat.gcd_eq_right hdiv
  calc
    addOrderOf ((n / d) • P)
        = addOrderOf P / Nat.gcd (addOrderOf P) (n / d) := by
            exact addOrderOf_nsmul P (n / d)
    _ = n / Nat.gcd n (n / d) := by
            rw [hP]
    _ = n / (n / d) := by
            rw [hgcd]
    _ = d := hquot

/--
Prime-specialized version.  If `P` has order `n` and prime `p` divides `n`,
then `(n / p) • P` has order `p`.
-/
lemma addOrderOf_nsmul_div_eq_prime_of_prime_dvd
    {G : Type*} [AddGroup G] {P : G} {n p : ℕ}
    (hP : addOrderOf P = n)
    (hnpos : 0 < n)
    (hp : p.Prime)
    (hpdvd : p ∣ n) :
    addOrderOf ((n / p) • P) = p := by
  exact addOrderOf_nsmul_div_eq_of_dvd hP hnpos hp.pos hpdvd

end FLT
```

If your local Mathlib has a slightly different theorem name, run:

```lean
#check addOrderOf_nsmul
#check orderOf_pow
#check Nat.gcd_eq_right
#check Nat.mul_div_right
```

The proof above is the intended proof.  The only likely edits are theorem-name adjustments.

---

## Specializing to `HasRationalPointOfOrder`

Assuming FLT already has:

```lean
HasRationalPointOfOrder E n
```

meaning exactly:

```lean
∃ P : (E/ℚ).Point, addOrderOf P = n
```

or an equivalent exact-order formulation, add these lemmas.

```lean
import Mathlib
-- import the FLT file that defines `HasRationalPointOfOrder`

namespace FLT

open scoped BigOperators

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]

/--
If `E(Q)` has a point of exact order `n`, then for every positive divisor `d`
of `n`, it has a point of exact order `d`.
-/
theorem HasRationalPointOfOrder.of_dvd
    {n d : ℕ}
    (h : HasRationalPointOfOrder E n)
    (hnpos : 0 < n)
    (hdpos : 0 < d)
    (hd : d ∣ n) :
    HasRationalPointOfOrder E d := by
  rcases h with ⟨P, hP⟩
  exact ⟨(n / d) • P, addOrderOf_nsmul_div_eq_of_dvd hP hnpos hdpos hd⟩

/--
Prime divisor version: if `E(Q)` has a point of exact order `n`, and prime `p`
divides `n`, then `E(Q)` has a point of exact order `p`.
-/
theorem HasRationalPointOfOrder.of_prime_dvd
    {n p : ℕ}
    (h : HasRationalPointOfOrder E n)
    (hnpos : 0 < n)
    (hp : p.Prime)
    (hpdvd : p ∣ n) :
    HasRationalPointOfOrder E p := by
  exact h.of_dvd hnpos hp.pos hpdvd

end FLT
```

This is the exact Lean formalization of the key lemma:

```text
if P has order n and p | n is prime, then (n/p) • P has order p.
```

Use additive scalar multiplication:

```lean
(n / p) • P
```

not multiplicative notation.

---

## Critical composite orders

To make the A-Line reduction true, introduce the finite list of minimal forbidden composite divisors.  These are the composite orders that must be excluded separately once the prime-order theorem is split off.

```lean
import Mathlib

namespace FLT

/--
Minimal forbidden composite divisors for the cyclic torsion A-Line, after the
prime-order case `p >= 11` is separated out.

Every integer `n >= 17` with no prime divisor `>= 11` has one of these as a
divisor, unless `n` is already in the small allowed list
`1,2,3,4,5,6,7,8,9,10,12`.
-/
inductive CriticalComposite : ℕ → Prop
  | n14 : CriticalComposite 14
  | n15 : CriticalComposite 15
  | n16 : CriticalComposite 16
  | n18 : CriticalComposite 18
  | n20 : CriticalComposite 20
  | n21 : CriticalComposite 21
  | n24 : CriticalComposite 24
  | n25 : CriticalComposite 25
  | n27 : CriticalComposite 27
  | n35 : CriticalComposite 35
  | n49 : CriticalComposite 49

lemma CriticalComposite.pos {d : ℕ} (hd : CriticalComposite d) : 0 < d := by
  cases hd <;> norm_num

end FLT
```

The list has a simple purpose:

```text
16,25,27,49   bound high prime powers 2^4,5^2,3^3,7^2;
14,15,18,20,21,24,35   exclude mixed products not dividing the Mazur allowed list.
```

For example:

```text
18 has only prime factors 2 and 3, so no large prime divisor;
20 has only prime factors 2 and 5;
21 has only prime factors 3 and 7;
25 has only prime factor 5;
27 has only prime factor 3;
49 has only prime factor 7.
```

These are exactly why the unconditional prime-order conclusion is false.

---

## Pure arithmetic lemma

The arithmetic part should be isolated from elliptic curves.

```lean
import Mathlib

namespace FLT

/--
Pure arithmetic reduction.

If `n >= 17`, then either `n` has a prime divisor `p >= 11`, or `n` has one of
the critical composite divisors.
-/
lemma large_nat_has_large_prime_or_critical_dvd
    {n : ℕ} (hn : 17 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p ∣ n) ∨
      ∃ d : ℕ, CriticalComposite d ∧ d ∣ n := by
  -- This is a pure `Nat` lemma.  Recommended proof:
  --
  -- 1. If there is a prime divisor `p >= 11`, finish.
  -- 2. Otherwise all prime divisors are in `{2,3,5,7}`.
  -- 3. If no critical composite divides `n`, then factorization exponents satisfy:
  --      v2 <= 3, v3 <= 2, v5 <= 1, v7 <= 1,
  --    plus the mixed exclusions from `14,15,18,20,21,24,35`.
  -- 4. The remaining possibilities are exactly
  --      1,2,3,4,5,6,7,8,9,10,12,
  --    contradicting `17 <= n`.
  --
  -- This can be proved with `Nat.factorization`, or by a finite exponent-case
  -- certificate over the primes `2,3,5,7`.
  sorry

end FLT
```

This lemma is not the hard arithmetic geometry.  It is just a finite arithmetic certificate.  It can remain local to the reduction file and should not be an axiom in the final theorem if you want a clean dependency graph.

---

## Correct disjunctive reduction theorem

This theorem is the honest replacement for the false unconditional statement.

```lean
import Mathlib
-- import the FLT file that defines `HasRationalPointOfOrder`
-- import the file containing `CriticalComposite`
-- import the file containing `large_nat_has_large_prime_or_critical_dvd`

namespace FLT

open scoped BigOperators

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]

/--
Correct order-divisor reduction.

A rational point of exact order `n >= 17` gives either a rational point of prime
order `p >= 11`, or a rational point of one of the critical composite orders.
-/
theorem has_large_prime_order_or_critical_composite_order_of_order_ge17
    {n : ℕ}
    (hn : 17 ≤ n)
    (h : HasRationalPointOfOrder E n) :
    (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ HasRationalPointOfOrder E p) ∨
      ∃ d : ℕ, CriticalComposite d ∧ HasRationalPointOfOrder E d := by
  have hnpos : 0 < n := by omega
  rcases large_nat_has_large_prime_or_critical_dvd (n := n) hn with hprime | hcrit
  · rcases hprime with ⟨p, hp, hp11, hpdvd⟩
    left
    exact ⟨p, hp, hp11, h.of_prime_dvd hnpos hp hpdvd⟩
  · rcases hcrit with ⟨d, hdcrit, hddvd⟩
    right
    exact ⟨d, hdcrit, h.of_dvd hnpos (CriticalComposite.pos hdcrit) hddvd⟩

end FLT
```

This is the theorem you can prove before proving any composite exclusions.

---

## Conditional prime-order reduction after composite exclusions

Once the finite composite exclusions are available, the theorem the user originally wanted becomes true.

```lean
import Mathlib
-- import the FLT file that defines `HasRationalPointOfOrder`
-- import the reduction theorem above

namespace FLT

open scoped BigOperators

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]

/--
After excluding the critical composite orders, any point of order `n >= 17`
forces a point of prime order `p >= 11`.
-/
theorem exists_large_prime_order_of_order_ge17
    {n : ℕ}
    (hn : 17 ≤ n)
    (h : HasRationalPointOfOrder E n)
    (hnoCrit : ∀ {d : ℕ}, CriticalComposite d → ¬ HasRationalPointOfOrder E d) :
    ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ HasRationalPointOfOrder E p := by
  rcases has_large_prime_order_or_critical_composite_order_of_order_ge17
      (E := E) hn h with hprime | hcrit
  · exact hprime
  · rcases hcrit with ⟨d, hdcrit, hdpoint⟩
    exact False.elim ((hnoCrit hdcrit) hdpoint)

end FLT
```

This is the concrete A-Line reduction that should feed the temporary axiom:

```lean
axiom no_point_of_prime_order_ge_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ HasRationalPointOfOrder E p
```

Together with composite exclusions:

```lean
axiom no_point_of_critical_composite_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {d : ℕ}
    (hd : CriticalComposite d) :
    ¬ HasRationalPointOfOrder E d
```

one derives:

```lean
import Mathlib

namespace FLT

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]

/--
No rational point of exact order at least `17`, derived from the prime core plus
finite composite exclusions.
-/
theorem no_point_of_order_ge17
    {n : ℕ}
    (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n := by
  intro h
  have hprime : ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ HasRationalPointOfOrder E p := by
    exact exists_large_prime_order_of_order_ge17
      (E := E) hn h
      (by
        intro d hdcrit hdpoint
        exact (no_point_of_critical_composite_order E hdcrit) hdpoint)
  rcases hprime with ⟨p, hp, hp11, hpPoint⟩
  exact (no_point_of_prime_order_ge_11 E hp hp11) hpPoint

end FLT
```

---

## Why the lcm contrapositive is not enough

The attempted contrapositive

```text
if there is no point of prime order >= 11,
then every element has order dividing lcm(1,...,10) = 2520
```

is not valid.

No large prime-order point only tells you that prime divisors of the order are among

```text
2,3,5,7.
```

It does not bound the exponents.  An element of order `25`, `27`, or `49` has only small prime-order divisors, but its order does not fit the Mazur allowed list.  Similarly, mixed orders like `18`, `20`, and `21` have only small prime factors but are still forbidden.

That is why the finite critical-composite layer is necessary.

## Bottom line

Use this dependency graph:

```text
addOrderOf_nsmul_div_eq_of_dvd
  -> HasRationalPointOfOrder.of_dvd
  -> has_large_prime_order_or_critical_composite_order_of_order_ge17
  -> exists_large_prime_order_of_order_ge17, assuming critical composites excluded
  -> no_point_of_order_ge17, using the prime-order axiom and composite exclusions
```

Do **not** try to prove the unconditional prime-order reduction.  It is false.  The correct Lean theorem is the disjunctive reduction, followed by the conditional prime-order theorem after the finite composite exclusions are installed.
