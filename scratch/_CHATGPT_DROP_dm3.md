# Q1141 (dm3): Mazur A-Line and `no_rational_point_of_order_ge_17`

## Bottom line

The realistic Lean path is **not** option A as stated.

```text
case-by-case 17..36 + Faltings for n ≥ 37
```

has two problems:

1. It is not mathematically sufficient.  A point of order `49`, for example, has no divisor in `17..36`; a point of prime order `37`, `41`, `43`, ... also has no divisor in `17..36`.
2. Faltings, even if available, only gives finiteness of `X₁(n)(ℚ)` when the genus is at least `2`.  It does **not** prove that the rational points are only cusps.  The missing step is essentially the hard part of Mazur/Kamienny/Parent style arguments.

The most realistic zero-axiom path is:

```text
formalize a Mazur cyclic-torsion theorem as a separate major module,
then derive `no_rational_point_of_order_ge_17` as a tiny corollary.
```

For the current theorem, the clean final dependency should be one of these:

```lean
rational_point_order_le_twelve :
  HasRationalPointOfOrder E n → n ≤ 12
```

or the sharper classification

```lean
rational_point_order_mem_mazur_list :
  HasRationalPointOfOrder E n →
    n ∈ ({1,2,3,4,5,6,7,8,9,10,12} : Finset ℕ)
```

Then `17 ≤ n` gives a contradiction by arithmetic only.

But if the goal is to discharge the axiom by a staged proof rather than one giant theorem, I would split the work into:

1. an elementary **order-divisor reduction**;
2. a finite list of **composite critical orders** handled by explicit modular-curve certificates;
3. the infinite **prime-order theorem** `no rational point of prime order p ≥ 11`, which is the real Mazur input.

That is the most concrete feasible plan.

## What Mathlib/FLT currently gives you

The FLT branch pins Mathlib at revision `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.  In that surface, the available elliptic-curve API is useful for Weierstrass curves and division-polynomial work, but there is no usable stack of:

```text
X₁(n), compactified modular curves, cusp classification,
genus formulas for X₁(n), Jacobians of X₁(n),
Faltings theorem, Chabauty, Mordell-Weil sieve,
Mazur's formal immersion theorem.
```

So a short proof is not hidden in Mathlib.  The project needs to contribute a serious Mazur module, or import one later after it exists upstream.

## Why option A is not enough

Suppose we prove, by computation, that there is no rational point of exact order

```text
17, 18, ..., 36.
```

This still does not rule out:

```text
49, 55, 77, 121, 37, 41, 43, ...
```

For example:

* a point of order `49` only gives points of order `7` and `49` by taking multiples;
* a point of order `37` only gives points of order `37` and `1`;
* a point of order `55` gives points of order `5`, `11`, and `55`.

Thus `17..36` is not a divisor-complete obstruction set.

Also, Faltings does not solve the tail.  For `genus X₁(n) ≥ 2`, Faltings gives:

```text
X₁(n)(ℚ) is finite.
```

What we need is:

```text
all points of X₁(n)(ℚ) are cusps.
```

Finiteness is far weaker.  In Lean, even if Faltings were available, one would still need a rational-point classification theorem for every relevant `X₁(n)`, or a uniform Mazur-style argument proving that all such points are cuspidal.

So option A should be replaced by:

```text
finite composite certificates + infinite prime-order Mazur theorem.
```

## The right arithmetic reduction

Define the cyclic allowed orders:

```text
1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12.
```

A divisor argument says: if `P` has exact order `n` and `d ∣ n`, then a suitable multiple of `P` has exact order `d`.

Therefore, to prove no order `n ≥ 17`, it is enough to prove:

1. no rational point of prime order `p ≥ 11`; and
2. no rational point of exact order in the finite composite critical list

   ```text
   14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 35, 49.
   ```

The list contains the minimal composite orders outside Mazur's allowed cyclic list, with respect to divisibility.  Once those are ruled out, any larger composite order has one of them as a divisor unless it has a prime divisor `≥ 11`.

This is much better than `17..36`: it includes the below-17 obstructions `14`, `15`, `16`, which are needed to rule out multiples such as `28`, `30`, `32`, `42`, `45`, and it includes `49`, which is invisible to the interval `17..36`.

The Lean shape should be:

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur

-- Project definition, shown only for context:
-- def HasRationalPointOfOrder (E : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
--   ∃ P : (E⁄ℚ).Point, addOrderOf P = n

/-- Composite minimal forbidden cyclic orders in Mazur's theorem. -/
def criticalCompositeOrders : Finset ℕ :=
  ({14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 35, 49} : Finset ℕ)

/--
Order divisor reduction.

If `P` has exact order `n` and `d ∣ n`, then `(n / d) • P` has exact order `d`.
This should be proved from the Mathlib order-of-a-multiple lemma for additive groups.
-/
theorem hasRationalPointOfOrder_of_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {d n : ℕ} (hdpos : 0 < d) (hdn : d ∣ n)
    (h : HasRationalPointOfOrder E n) :
    HasRationalPointOfOrder E d := by
  -- Choose `P` of order `n`.
  -- Let `Q = (n / d) • P`.
  -- Use `addOrderOf_nsmul` or the corresponding Mathlib theorem to show
  -- `addOrderOf Q = d`.
  -- This is elementary group theory, not Mazur.
  sorry

/-- Pure arithmetic reduction. -/
theorem exists_prime_ge_eleven_or_criticalComposite_dvd
    {n : ℕ} (hn : 17 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p ∣ n) ∨
      ∃ d : ℕ, d ∈ criticalCompositeOrders ∧ d ∣ n := by
  -- Formalizable from `Nat.factorization`.
  -- Sketch:
  --   * if some prime divisor `p` of `n` has `11 ≤ p`, use the left branch;
  --   * otherwise all prime divisors are in `{2,3,5,7}`;
  --   * inspect the exponents of `2,3,5,7`;
  --   * if no critical order divides `n`, then `n` is one of
  --       `1,2,3,4,5,6,7,8,9,10,12`, contradicting `17 ≤ n`.
  sorry

/-- Prime-order Mazur theorem.  This is the infinite hard theorem. -/
theorem no_prime_rational_point_of_order_ge_eleven
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ HasRationalPointOfOrder E p := by
  -- This is not a finite computation.  It is the main Mazur input.
  -- See the plan below.
  sorry

/-- Finite composite certificates. -/
theorem no_criticalComposite_rational_point_of_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {d : ℕ} (hd : d ∈ criticalCompositeOrders) :
    ¬ HasRationalPointOfOrder E d := by
  -- This should dispatch to per-level certificate theorems:
  --   d = 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 35, 49.
  -- Each per-level theorem comes from an explicit `X₁(d)` model plus a
  -- machine-checkable rational-point certificate.
  sorry

/-- The current FLT target, after the Mazur inputs are available. -/
theorem no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n := by
  intro h
  rcases exists_prime_ge_eleven_or_criticalComposite_dvd hn with
    ⟨p, hp, hp11, hpn⟩ | ⟨d, hdcrit, hdn⟩
  · exact
      (no_prime_rational_point_of_order_ge_eleven E hp hp11)
        (hasRationalPointOfOrder_of_dvd E hp.pos hpn h)
  · have hdpos : 0 < d := by
      -- follows by finite checking from `hdcrit`
      fin_cases hdcrit <;> norm_num
    exact
      (no_criticalComposite_rational_point_of_order E hdcrit)
        (hasRationalPointOfOrder_of_dvd E hdpos hdn h)

end FLT.Mazur
```

The final theorem above is only wiring.  The hard parts are explicitly isolated.

## What can be computationally verified?

The finite composite list is the best computational target:

```text
14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 35, 49.
```

For each fixed `N` in this list, the following strategy is plausible:

1. Use Tate normal form / Kubert normal form to reduce an elliptic curve with a rational point of order `N` to a rational point on an explicit curve `C_N`.
2. Provide an explicit birational map between `C_N` and a known model of `X₁(N)` or an equivalent parameter curve.
3. Prove that rational points on `C_N` are exactly the cusps / degenerate points.
4. Conclude that no nonsingular elliptic curve over `ℚ` has a rational point of exact order `N`.

In Lean, the key is not to trust Magma/Sage output.  Use Magma/Sage to **generate certificates**, then replay those certificates in Lean.

Examples of certificate styles:

* finite-field point counts: Lean verifies polynomial arithmetic over `ZMod p`;
* genus computations for a fixed plane model: Lean verifies adjunction/singularity data for the explicit model;
* elliptic-curve rank-zero certificates: Lean verifies a descent or an `L`-value/rank certificate only after the necessary infrastructure exists;
* Mordell-Weil sieve / Chabauty certificates: Lean verifies the finite residue computations and the rank/input hypotheses;
* explicit divisor/principal-function certificates: Lean checks that a given rational function has the claimed divisor, reducing a rational-point claim to finite algebra.

The finite cases are feasible because they are fixed, explicit, and certificate-generating.  They are still not one-line `norm_num` computations: global rational-point classification is arithmetic geometry, even for a fixed curve.

## What is the infinite hard theorem?

The genuinely infinite theorem is:

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur

/-- Prime cyclic-torsion exclusion over `ℚ`. -/
theorem no_prime_rational_point_of_order_ge_eleven
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ HasRationalPointOfOrder E p := by
  sorry

end FLT.Mazur
```

This is not a finite computation.  This is where a real Mazur proof enters.

The most plausible formal proof is Mazur's modular-curve/formal-immersion argument, not Faltings.  In broad strokes:

```text
rational point P of order p
  ⇒ noncuspidal rational point on X₁(p)
  ⇒ associated point on a Jacobian / Eisenstein quotient
  ⇒ formal immersion at a cusp plus reduction arguments
  ⇒ contradiction for p ≥ 11.
```

For Lean, this would require developing:

* a usable definition of `X₁(p)` or an explicit substitute;
* cusps and the map from elliptic curves with a marked point to `X₁(p)`;
* integral models and reduction modulo primes;
* Jacobians or a certificate-level substitute for the needed formal immersion;
* enough modular-symbol/Hecke/Eisenstein-ideal computation to certify the formal immersion statement.

This is the hardest part of the whole project.  But it is the right infinite theorem.  Replacing it by Faltings does not work.

## Does Mathlib have genus formulas for `X₁(n)`?

No usable `X₁(n)` genus API is available in the current FLT/Mathlib surface.

There are general algebraic-geometry and modular-form libraries, but not the package one would need:

```lean
ModularCurve.X1
ModularCurve.X1.genus
ModularCurve.X1.cusps
ModularCurve.X1.rationalPoints_eq_cusps
```

So for the finite cases, do not wait for a general genus formula.  Use explicit models and per-level certificates.

A good per-level interface is:

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur

/-- A certificate theorem for a fixed level. -/
theorem no_rational_point_of_order_14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 14 := by
  -- Derived from an explicit `X₁(14)`/Tate-normal-form certificate.
  sorry

/-- Same pattern for each finite composite critical level. -/
theorem no_rational_point_of_order_49
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 49 := by
  -- This one is important because `49` is missed by the naive `17..36` range.
  sorry

end FLT.Mazur
```

Later, replace each `sorry` by a certificate proof.  The theorem names can remain stable.

## Does Mathlib have Faltings theorem for this application?

No.  More importantly, Faltings would not be the right tool for this theorem even if it existed.

A hypothetical theorem

```lean
Curve.rationalPoints_finite_of_genus_ge_two
```

would only prove that `X₁(n)(ℚ)` is finite.  It would not classify the finite set.  To prove absence of noncuspidal points, one needs additional arithmetic: Chabauty, Mordell-Weil sieve, formal immersion, or explicit descent/certificates.

So the Lean plan should not contain a dependency of the form:

```text
use Faltings for all n ≥ 37
```

Instead use:

```text
use Mazur's prime-order theorem for the infinite prime tail,
use explicit certificates for finite composite critical orders.
```

## Recommended module plan

### 1. `FLT/Mazur/OrderReduction.lean`

Prove pure group/order arithmetic.

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur

-- exact statement should use the project's point type

theorem hasRationalPointOfOrder_of_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {d n : ℕ} (hdpos : 0 < d) (hdn : d ∣ n)
    (h : HasRationalPointOfOrder E n) :
    HasRationalPointOfOrder E d := by
  sorry

def criticalCompositeOrders : Finset ℕ :=
  ({14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 35, 49} : Finset ℕ)

theorem exists_prime_ge_eleven_or_criticalComposite_dvd
    {n : ℕ} (hn : 17 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p ∣ n) ∨
      ∃ d : ℕ, d ∈ criticalCompositeOrders ∧ d ∣ n := by
  sorry

end FLT.Mazur
```

This file is very feasible now.

### 2. `FLT/Mazur/TateNormalForm.lean`

Formalize the algebraic normal form:

```text
E_{b,c}: y² + (1-c)xy - by = x³ - bx²,
P = (0,0).
```

Show that an elliptic curve over `ℚ` with a rational point of order `N ≥ 4` is isomorphic, preserving the marked point, to a Tate-normal-form curve for some rational parameters `b,c` satisfying the exact-order conditions.

This avoids building the full moduli stack at first.  It gives a concrete bridge from `HasRationalPointOfOrder E N` to rational points on explicit parameter curves.

### 3. `FLT/Mazur/X1ExplicitModels.lean`

For each finite critical `N`, define the explicit model used for `X₁(N)` or the relevant parameter curve.

Each model should come with:

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur

structure X1ModelCertificate (N : ℕ) where
  -- Placeholder for the actual certificate data:
  -- equations, maps, cusp set, rational-point certificate, etc.
  dummy : True

end FLT.Mazur
```

The point is not the dummy structure; the point is the architecture: every theorem should check a concrete certificate, not trust an external CAS.

### 4. `FLT/Mazur/FiniteComposite.lean`

Provide one theorem for each critical composite order and a dispatcher.

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur

theorem no_criticalComposite_rational_point_of_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {d : ℕ} (hd : d ∈ criticalCompositeOrders) :
    ¬ HasRationalPointOfOrder E d := by
  fin_cases hd
  all_goals
    -- dispatch to the corresponding certificate theorem
    sorry

end FLT.Mazur
```

This finite dispatcher is straightforward after the per-level certificates exist.

### 5. `FLT/Mazur/PrimeTorsion.lean`

This is the main theorem:

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur

theorem no_prime_rational_point_of_order_ge_eleven
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ HasRationalPointOfOrder E p := by
  sorry

end FLT.Mazur
```

This should be attacked by Mazur's modular-curve/formal-immersion method, or by a future upstream formalization of that theorem.  This is not currently a small Mathlib wiring task.

### 6. `FLT/Mazur/NoOrderGe17.lean`

Finally, the current theorem becomes:

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur

theorem no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n := by
  intro h
  rcases exists_prime_ge_eleven_or_criticalComposite_dvd hn with
    ⟨p, hp, hp11, hpn⟩ | ⟨d, hdcrit, hdn⟩
  · exact
      (no_prime_rational_point_of_order_ge_eleven E hp hp11)
        (hasRationalPointOfOrder_of_dvd E hp.pos hpn h)
  · have hdpos : 0 < d := by
      fin_cases hdcrit <;> norm_num
    exact
      (no_criticalComposite_rational_point_of_order E hdcrit)
        (hasRationalPointOfOrder_of_dvd E hdpos hdn h)

end FLT.Mazur
```

This is the proof shape I would aim for.

## Practical priority order

1. Prove the order-divisor lemma.
2. Prove the arithmetic reduction to `prime ≥ 11` or the finite critical composite list.
3. Formalize Tate normal form enough to connect rational torsion to explicit parameter curves.
4. Pick the easiest finite composite level first, produce a full certificate proof, and use it as the template.
5. Build the finite dispatcher for all critical composite orders.
6. Treat `no_prime_rational_point_of_order_ge_eleven` as the separate Mazur-prime project.

The infinite prime theorem is the bottleneck.  No amount of finite checking for `17..36` removes it.

## Final recommendation

Do not spend effort on a general `X₁(n)` genus formula or on Faltings as the first milestone.  They will not close this theorem.

The shortest realistic path is:

```text
Order arithmetic now;
explicit finite composite certificates next;
Mazur prime-order theorem as the main long-term formalization target;
`no_rational_point_of_order_ge_17` as the final short corollary.
```

This gives a zero-axiom roadmap with a clear separation between easy Lean work, finite certificate work, and the genuinely hard Mazur theorem.
