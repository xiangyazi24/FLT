# Q1146 (dm2): A-Line prime torsion core and a practical Mazur split

## Executive answer

For the A-Line cyclic torsion theorem, the right split is exactly the one suggested:

```text
1. finite group/order-divisor reduction;
2. explicit composite-order exclusions;
3. one hard prime-order theorem:

   no rational point of prime order p >= 11.
```

The third item is the mathematical core of the prime part of Mazur's torsion theorem.  There is no genuinely elementary uniform proof avoiding modular curves.  Merel/Kamienny do not avoid modular curves; they are deeper modular-curve/uniform-boundedness arguments and are much larger than what is needed here.  Pure descent arguments can handle fixed small levels such as `11` and sometimes `13`, but they do not give a uniform theorem for all primes `p >= 17`.

So the shortest honest FLT architecture is:

```lean
axiom no_point_of_prime_order_ge_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 <= p) :
    ¬ HasPointOfExactOrder E p
```

plus finite composite-order certificates.  Then derive the broad theorem

```lean
theorem no_point_of_order_ge_17
```

by pure group theory and pure arithmetic.

This is a very good split: it isolates the hardest modular-curve theorem and lets the rest of the A-Line become formal, auditable, and small.

---

## (a) Can the prime-order theorem avoid modular curves?

### Uniform statement `p >= 11` or `p >= 13`

For the uniform theorem

```text
there is no elliptic curve over Q with a rational point of prime order p >= 11,
```

all known short proofs are modular-curve proofs in substance.

The reason is structural.  A pair `(E, P)` with `P` of exact order `p` is a rational noncuspidal point of the modular curve `X_1(p)`.  Proving nonexistence is exactly the assertion that

```text
X_1(p)(Q) has no noncuspidal rational points, for p >= 11.
```

That is the prime-level part of Mazur's theorem.

### Merel

Merel's uniform boundedness theorem is not a shortcut here.

It proves that torsion over degree-`d` number fields is uniformly bounded, but:

```text
- it is much deeper than the prime-order part needed here;
- its proof uses modular curves / geometry of modular curves;
- it does not by itself give the sharp Q-bound excluding p = 11, 13, ...;
- even an effective Merel-style bound would leave many primes to check unless a sharp bound is already known.
```

So Merel is a theorem one could use as a black box only if Mathlib already had a very sharp specialization to `Q`.  It is not a smaller formalization target.

### Kamienny

Kamienny's criterion is also modular-curve technology.  It is useful historically and mathematically for uniform boundedness, but it is not simpler than the prime Mazur theorem for the FLT purpose.

### Pure descent

There is no known clean descent-only proof for all primes `p >= 11` that avoids modular curves.  Descent enters after one has an explicit modular curve model, especially for fixed `N`.

So the answer to (a) is:

```text
No, not uniformly.  For fixed N one can do explicit descent on X_1(N),
but the uniform prime theorem is modular-curve content.
```

---

## (b) Smallest self-contained mathematical module to formalize

The smallest useful formal module is not a full formalization of Mazur's proof.  It is a narrow interface theorem plus elementary reductions.

### Minimal hard axiom

Use this as the core hard theorem:

```lean
import Mathlib

namespace FLT

/--
A point of exact additive order `n` on `E(Q)`.
Replace `(E⧸ℚ).Point` with the actual point type used in FLT.
-/
def HasPointOfExactOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⧸ℚ).Point, addOrderOf P = n

/--
Prime-order Mazur core.
Mathematical content: `X_1(p)(Q)` has no noncuspidal points for prime `p >= 11`.
Keep this as the temporary hard axiom.
-/
axiom no_point_of_prime_order_ge_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 <= p) :
    ¬ HasPointOfExactOrder E p

end FLT
```

This is a better axiom than a broad `no_large_torsion` theorem because it names the actual mathematical core.

### Finite composite certificates

Use a finite predicate for the minimal forbidden composite orders:

```lean
import Mathlib

namespace FLT

/--
Minimal forbidden composite divisors for cyclic torsion over `Q`, once the prime
case `p >= 11` is separated out.

These are the composite `d` such that all proper divisors of `d` are in
Mazur's cyclic allowed list `{1,2,3,4,5,6,7,8,9,10,12}`, but `d` itself is not.
-/
inductive CriticalComposite : ℕ -> Prop
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

/--
Composite-order exclusions.  Prove these one by one using Kubert/descent
certificates, or keep individual entries as axioms while building the certificates.
-/
axiom no_point_of_critical_composite_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : CriticalComposite n) :
    ¬ HasPointOfExactOrder E n

end FLT
```

Why this exact list?

If a point has exact order `N`, then for every divisor `d | N` it gives a point of exact order `d`.  Therefore to exclude all cyclic orders not in

```text
1,2,3,4,5,6,7,8,9,10,12
```

it suffices to exclude:

```text
prime p >= 11,
14,15,16,18,20,21,24,25,27,35,49.
```

For example:

```text
28 has divisor 14,
30 has divisor 15,
32 has divisor 16,
36 has divisor 18,
40 has divisor 20,
42 has divisor 14 or 21,
45 has divisor 15,
50 has divisor 25,
63 has divisor 21 or 27,
70 has divisor 14 or 35.
```

The prime powers `16`, `27`, `25`, and `49` are needed to bound the exponents of `2`, `3`, `5`, and `7` after large primes have been ruled out.

### Divisor reduction lemma

The group-theory lemma needed is small and reusable:

```lean
import Mathlib

namespace FLT

/--
Pure group theory: if an additive group has an element of exact order `n`, then
it has an element of exact order every positive divisor `d` of `n`.
-/
lemma exists_exact_order_of_dvd_exact_order
    {G : Type*} [AddGroup G] {n d : ℕ}
    (hdpos : 0 < d) (hd : d ∣ n)
    (hG : ∃ P : G, addOrderOf P = n) :
    ∃ Q : G, addOrderOf Q = d := by
  rcases hG with ⟨P, hP⟩
  rcases hd with ⟨k, rfl⟩
  -- Take `Q = k • P`.  The standard theorem is the additive version of
  -- `orderOf_pow`; depending on the Mathlib name, use either `addOrderOf_nsmul`
  -- or port the multiplicative theorem by `toAdditive`.
  -- Expected mathematical calculation:
  --   addOrderOf (k • P) = addOrderOf P / Nat.gcd (addOrderOf P) k
  -- and with `addOrderOf P = d * k`, this is `d`.
  sorry

end FLT
```

This lemma is not elliptic-curve specific.  It should be proved once in a group-theory helper file.

### Arithmetic divisor lemma

The number-theory lemma is also independent of elliptic curves:

```lean
import Mathlib

namespace FLT

/--
Arithmetic core of the order-divisor reduction.

If `n >= 17`, then either `n` has a prime divisor `p >= 11`, or it has one of
Mazur's minimal forbidden composite divisors.
-/
lemma exists_prime_ge_11_or_critical_composite_dvd
    {n : ℕ} (hn : 17 <= n) :
    (∃ p : ℕ, p.Prime ∧ 11 <= p ∧ p ∣ n) ∨
      ∃ d : ℕ, CriticalComposite d ∧ d ∣ n := by
  -- Recommended proof strategy:
  -- 1. If there is a prime factor `p >= 11`, done.
  -- 2. Otherwise all prime factors are in `{2,3,5,7}`.
  -- 3. If no critical composite divides `n`, then valuations satisfy:
  --      v2 <= 3, v3 <= 2, v5 <= 1, v7 <= 1,
  --    plus compatibility exclusions from `14,15,18,20,21,24,35`.
  -- 4. Enumerate the remaining possibilities and show `n <= 12`, contradiction.
  --
  -- This can be formalized using `Nat.factorization` and a small finite case split.
  sorry

end FLT
```

This is much smaller than any modular-curve formalization and should be part of the non-axiomatic reduction layer.

### Derived theorem: no cyclic order `>= 17`

Now the broad theorem follows mechanically:

```lean
import Mathlib

namespace FLT

/--
Derived theorem: no rational point of exact order `n >= 17`, assuming the prime
Mazur core and the finite composite certificates.
-/
theorem no_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 <= n) :
    ¬ HasPointOfExactOrder E n := by
  intro hN
  have hdiv := exists_prime_ge_11_or_critical_composite_dvd (n := n) hn
  cases hdiv with
  | inl hpcase =>
      rcases hpcase with ⟨p, hp, hp11, hpdvd⟩
      have hppos : 0 < p := hp.pos
      have hp_point : HasPointOfExactOrder E p := by
        -- apply the group-theory divisor lemma to the point group `(E⧸ℚ).Point`
        -- using `hpdvd` and `hN`.
        sorry
      exact (no_point_of_prime_order_ge_11 E hp hp11) hp_point
  | inr hdcase =>
      rcases hdcase with ⟨d, hdcrit, hddvd⟩
      have hdpos : 0 < d := by
        cases hdcrit <;> decide
      have hd_point : HasPointOfExactOrder E d := by
        -- apply the same group-theory divisor lemma.
        sorry
      exact (no_point_of_critical_composite_order E hdcrit) hd_point

end FLT
```

The only remaining `sorry`s here are not deep:

```text
- connect `HasPointOfExactOrder E n` to the generic group-theory divisor lemma;
- prove the arithmetic divisor lemma.
```

The hard mathematics is entirely contained in:

```text
no_point_of_prime_order_ge_11
no_point_of_critical_composite_order
```

and the latter is finite/certificate-driven.

---

## (c) What about primes 11 and 13 specifically?

### Prime 11

For `p = 11`, there is a much smaller proof than the full Mazur theorem.

A rational point of order `11` gives a rational noncuspidal point on `X_1(11)`.  The curve `X_1(11)` has genus `1`.  One can use an explicit model from Tate/Kubert normal form, identify it with an elliptic curve of rank `0`, compute its rational points, and check that all rational points are cusps.

This is not fully elementary in the sense of high-school algebra, but it is a finite descent/rank computation on a specific elliptic curve.  It avoids the general Mazur machinery.

A feasible formal module for `p = 11` would be:

```text
1. Tate normal form for a point of order 11.
2. Transformation to a fixed genus-one model for X_1(11).
3. A rank-zero / finite-rational-points certificate for that model.
4. A check that the finite rational points are all cuspidal/degenerate.
```

This is plausible if FLT already has Kubert parametrization machinery.

### Prime 13

For `p = 13`, the curve `X_1(13)` has genus `2`.  There are explicit hyperelliptic models, and the rational points can be determined by methods such as descent on the Jacobian plus a Mordell-Weil sieve or Chabauty-style arguments.

This is still far smaller than all of Mazur's theorem, but it is not a tiny elementary descent.  It requires a rational-points certificate on a genus-two curve.

A feasible formal module for `p = 13` would be:

```text
1. Tate/Kubert normal form for order 13.
2. A map to an explicit genus-two model of X_1(13).
3. A certified finite list of rational points on that curve.
4. A check that all listed points are cusps/degenerate.
```

If the existing `QuarticD` infrastructure proves rational-point nonexistence or finite rational-point lists for quartic/hyperelliptic curves, it may help here.  But this is still a fixed-level modular-curve proof.

### Prime `p >= 17`

For all primes `p >= 17`, fixed-level descent is no longer a practical uniform strategy.  You would need one model and one rational-points computation for infinitely many modular curves `X_1(p)`.  That is exactly what Mazur's method avoids by using a general modular-curve argument.

So the sensible split is:

```text
- maybe prove p = 11 explicitly;
- maybe prove p = 13 explicitly if the genus-two infrastructure is ready;
- keep p >= 17 as the true prime Mazur axiom;
```

or, even simpler for now:

```text
keep one axiom for all prime p >= 11.
```

The latter is cleaner while the A-Line is still being assembled.

---

## Can the existing Kubert/QuarticD/DescentBridge infrastructure help?

Yes, but only for fixed levels and finite composite certificates.

### Where it helps

The user-mentioned infrastructure sounds directly relevant for:

```text
N = 14,
N = 16,
and probably other fixed composite critical levels if analogous files exist.
```

Kubert/Tate normal form is exactly the right entry point for turning a rational point of exact order `N` into a rational point on an explicit parameter curve.  A descent bridge can then show that this parameter curve has no nondegenerate rational points.

This is the right way to prove the finite composite exclusions:

```lean
no_point_of_critical_composite_order E CriticalComposite.n14
no_point_of_critical_composite_order E CriticalComposite.n16
```

and so on.

### Where it may help

It may also help for:

```text
N = 11,
N = 13,
N = 15,
N = 18,
N = 20,
N = 21,
N = 24,
N = 25,
N = 27,
N = 35,
N = 49.
```

For each fixed `N`, the pattern is:

```text
point of order N
  -> Tate/Kubert parameter satisfying explicit equations and nondegeneracy conditions
  -> rational point on a fixed auxiliary curve
  -> descent certificate says no such rational point
  -> contradiction.
```

The amount of work varies sharply with `N`.

### Where it does not help

It does not solve the uniform prime theorem

```text
no point of prime order p >= 17.
```

Kubert normal forms for arbitrary `p` would still leave infinitely many modular curves `X_1(p)`.  The missing theorem remains Mazur's prime-level argument.

---

## Recommended concrete plan

### Phase 1: isolate definitions and reductions

Create a file such as:

```text
FLT/Torsion/OrderReduction.lean
```

with:

```lean
import Mathlib

namespace FLT

-- Use the actual FLT point type here.
def HasPointOfExactOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⧸ℚ).Point, addOrderOf P = n

inductive CriticalComposite : ℕ -> Prop
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

lemma exists_exact_order_of_dvd_exact_order
    {G : Type*} [AddGroup G] {n d : ℕ}
    (hdpos : 0 < d) (hd : d ∣ n)
    (hG : ∃ P : G, addOrderOf P = n) :
    ∃ Q : G, addOrderOf Q = d := by
  sorry

lemma exists_prime_ge_11_or_critical_composite_dvd
    {n : ℕ} (hn : 17 <= n) :
    (∃ p : ℕ, p.Prime ∧ 11 <= p ∧ p ∣ n) ∨
      ∃ d : ℕ, CriticalComposite d ∧ d ∣ n := by
  sorry

end FLT
```

These are not Mazur-theorem files.  They are pure reduction files.

### Phase 2: introduce the hard interfaces

Create:

```text
FLT/Torsion/PrimeCore.lean
```

```lean
import Mathlib
import FLT.Torsion.OrderReduction

namespace FLT

/--
Prime-level Mazur core.  Temporary axiom.
Future proof target: modular curves `X_1(p)` have no noncuspidal rational points
for prime `p >= 11`.
-/
axiom no_point_of_prime_order_ge_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 <= p) :
    ¬ HasPointOfExactOrder E p

/--
Finite composite certificates.  Initially an axiom; replace constructor-by-constructor
using Kubert/QuarticD/DescentBridge files.
-/
axiom no_point_of_critical_composite_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : CriticalComposite n) :
    ¬ HasPointOfExactOrder E n

end FLT
```

This is the clean axiom boundary.

### Phase 3: derive the broad no-large-order theorem

Create:

```text
FLT/Torsion/NoLargeOrder.lean
```

```lean
import Mathlib
import FLT.Torsion.OrderReduction
import FLT.Torsion.PrimeCore

namespace FLT

/--
No rational point of exact cyclic order at least 17.
This is derived from the prime Mazur core plus finite composite exclusions.
-/
theorem no_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 <= n) :
    ¬ HasPointOfExactOrder E n := by
  intro hN
  rcases exists_prime_ge_11_or_critical_composite_dvd (n := n) hn with hprime | hcomp
  · rcases hprime with ⟨p, hp, hp11, hpdvd⟩
    have hp_point : HasPointOfExactOrder E p := by
      -- specialize `exists_exact_order_of_dvd_exact_order` to `(E⧸ℚ).Point`
      -- and use `hN`.
      sorry
    exact (no_point_of_prime_order_ge_11 E hp hp11) hp_point
  · rcases hcomp with ⟨d, hdcrit, hddvd⟩
    have hdpos : 0 < d := by
      cases hdcrit <;> decide
    have hd_point : HasPointOfExactOrder E d := by
      -- same divisor lemma.
      sorry
    exact (no_point_of_critical_composite_order E hdcrit) hd_point

end FLT
```

This theorem is a good derived target.  It should not itself be an axiom.

### Phase 4: replace composite axioms incrementally

Use the existing infrastructure in this order:

```text
1. N = 14 via DescentBridgeN14.
2. N = 16 via DescentBridgeN16.
3. Add analogous certificates for N = 15,18,20,21,24,25,27,35,49 as needed.
4. Optionally split p = 11 and p = 13 out of the prime axiom once their explicit modular-curve computations are available.
```

The prime axiom can then be narrowed over time:

```lean
axiom no_point_of_prime_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp17 : 17 <= p) :
    ¬ HasPointOfExactOrder E p
```

with separate proved theorems for `11` and `13`.

### Phase 5: final A-Line cyclic torsion theorem

Once `no_point_of_order_ge_17` is available, the remaining low orders are finite:

```text
allowed cyclic orders: 1,2,3,4,5,6,7,8,9,10,12
forbidden below 17: 11,13,14,15,16
```

The primes `11,13` are covered by the prime axiom.  The composites `14,15,16` are covered by the composite certificates.  Everything `>=17` is covered by `no_point_of_order_ge_17`.

So the final theorem should be a case split on `n`:

```lean
import Mathlib
import FLT.Torsion.NoLargeOrder

namespace FLT

/--
A-Line cyclic torsion bound, schematic.
-/
theorem cyclic_torsion_order_in_mazur_list
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hP : HasPointOfExactOrder E n) :
    n ∈ ({1,2,3,4,5,6,7,8,9,10,12} : Finset ℕ) := by
  by_cases hn17 : 17 <= n
  · exact False.elim ((no_point_of_order_ge_17 E hn17) hP)
  · -- finite check for n < 17:
    -- allowed: 1,2,3,4,5,6,7,8,9,10,12
    -- forbidden: 11,13 by prime axiom; 14,15,16 by composite certificates.
    sorry

end FLT
```

The finite `n < 17` branch should be handled by `omega` plus individual contradictions.

---

## Should the axiom be split?

Yes.

Do this:

```lean
axiom no_point_of_prime_order_ge_11
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 <= p) :
    ¬ HasPointOfExactOrder E p
```

and derive:

```lean
theorem no_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 <= n) :
    ¬ HasPointOfExactOrder E n
```

from that axiom plus finite composite exclusions.

This reduces the axiom to the true mathematical core and makes all remaining work transparent:

```text
- group theory: divisor of an exact-order point gives exact-order point;
- arithmetic: large integer has either large prime divisor or critical composite divisor;
- finite certificates: N = 14,15,16,18,20,21,24,25,27,35,49;
- hard modular theorem: prime p >= 11.
```

That is the cleanest plan for FLT.

## Bottom line

For `p >= 11`, the simplest known uniform proof is Mazur's modular-curve proof, not a descent-only or number-theory-only argument.  For `p = 11` and `p = 13`, one can use explicit modular-curve computations; `p = 11` is comparatively small, while `p = 13` needs genus-two rational-points machinery.  The existing Kubert/QuarticD/DescentBridge infrastructure is useful for fixed levels and finite composite certificates, and may help with `11` or `13`, but it does not replace the uniform prime theorem for `p >= 17`.

Therefore the concrete FLT plan is:

```text
1. Add `HasPointOfExactOrder` and pure divisor/order lemmas.
2. Add `CriticalComposite` with the 11 minimal forbidden composite orders.
3. Keep `no_point_of_prime_order_ge_11` as the single hard axiom.
4. Prove `no_point_of_order_ge_17` from the prime axiom plus composite certificates.
5. Replace composite axioms one by one using existing Kubert/descent files.
6. Optionally later split off explicit proofs for p = 11 and p = 13, narrowing the hard axiom to p >= 17.
```
