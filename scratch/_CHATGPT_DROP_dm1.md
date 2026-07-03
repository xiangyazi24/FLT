# Q3141 (dm1): Theorem 5 coefficient formula in Lean

Date: 2026-07-03

## Executive answer

Use option **(a)**: define `B_N` as a computable `Finset.sum` over an explicit bounded rectangle, filtered by the equation `E k r = N` and by the active same-sign cones.  Do **not** start with `Finsupp`, and do **not** start with `PowerSeries` as the primary definition.

The important correction is that the clean Lean statement should not literally sum over all pairs satisfying only

```text
E(k,r) = N.
```

The quadratic form is indefinite off the same-sign cones, and the mixed-cone solutions are irrelevant because `BWeight = 0` there.  The finite coefficient theorem should sum over

```text
E(k,r) = N  and  (InACone(k,r) or InDCone(k,r)).
```

So the right Lean-level definition is:

```lean
def Bcoeff (N : Nat) : Int :=
  ((atomBox N).filter (activeAtom N)).sum
    (fun p => BWeight p.1 p.2)
```

Then the theorem

```text
B_N = Σ BWeight(k,r)
```

is either literally `rfl`, or a one-line simp theorem, depending on how you name it.  The genuinely useful theorem is not this definitional equality; it is the **support-bound theorem** saying your chosen box contains every active atom with exponent `N`.

## Recommended formalization

Use a deliberately coarse bound.  Do not try to use square roots.  Let

```text
C(N) = 2N + 1.
```

Then every active same-sign-cone atom contributing to coefficient `N` lies in

```text
-C(N) <= k <= C(N),
-C(N) <= r <= C(N).
```

This bound is intentionally not sharp, but it is easy to prove and easy to use.

## Imports

For the coefficient file, start with:

```lean
import Mathlib.Tactic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset

import QseriesFormalization.Ch10.ConeAlgebra

open scoped BigOperators

namespace QseriesFormalization
namespace Ch10
```

If your umbrella file already imports `Mathlib.Tactic` and `Finset.Icc` works, you may not need all of these.  The two imports that matter conceptually are the interval finset API and finite sums.

## Core definitions

This is the path of least resistance.

```lean
import Mathlib.Tactic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset

import QseriesFormalization.Ch10.ConeAlgebra

open scoped BigOperators

namespace QseriesFormalization
namespace Ch10

/-- A coarse coefficient bound.  It is deliberately larger than necessary. -/
def coeffBound (N : Nat) : Int :=
  2 * (N : Int) + 1

/-- Integer range used for coefficient extraction. -/
def coeffRange (N : Nat) : Finset Int :=
  Finset.Icc (-(coeffBound N)) (coeffBound N)

/-- Candidate pairs for coefficient extraction. -/
def atomBox (N : Nat) : Finset (Int × Int) :=
  (coeffRange N).product (coeffRange N)

/-- Active atoms for the cone series coefficient. -/
def activeAtom (N : Nat) (p : Int × Int) : Prop :=
  E p.1 p.2 = (N : Int) ∧ (InACone p.1 p.2 ∨ InDCone p.1 p.2)

/-- Finite set of active atoms contributing to coefficient `N`. -/
def atomFinset (N : Nat) : Finset (Int × Int) :=
  (atomBox N).filter (activeAtom N)

/-- The coefficient of the cone-difference series `B(X)`. -/
def Bcoeff (N : Nat) : Int :=
  (atomFinset N).sum (fun p => BWeight p.1 p.2)

/-- The coefficient formula is definitional once `Bcoeff` is the definition. -/
theorem Bcoeff_eq_sum (N : Nat) :
    Bcoeff N = (atomFinset N).sum (fun p => BWeight p.1 p.2) := rfl

@[simp] theorem mem_atomFinset_iff (N : Nat) (p : Int × Int) :
    p ∈ atomFinset N ↔
      p ∈ atomBox N ∧ E p.1 p.2 = (N : Int) ∧
        (InACone p.1 p.2 ∨ InDCone p.1 p.2) := by
  simp [atomFinset, activeAtom]

end Ch10
end QseriesFormalization
```

This avoids `Finsupp` entirely.  It also avoids any need for a noncomputable definition.  Everything is a concrete finite sum.

## Why filter by cone membership?

Do not define the active finset as only

```lean
(E p.1 p.2 = (N : Int))
```

because off the same-sign cones the form is indefinite.  Even if `BWeight` is zero off the cones, Lean would still be asked to reason about a box that is not mathematically the full solution set of `E=N`.  The coefficient series itself is a same-sign-cone series, so make that explicit:

```lean
E p.1 p.2 = (N : Int) ∧ (InACone p.1 p.2 ∨ InDCone p.1 p.2)
```

This is both mathematically cleaner and much easier for Lean.

## The real theorem: the box contains all active atoms

The important theorem is the support theorem:

```lean
theorem activeAtom_mem_atomBox {N : Nat} {k r : Int}
    (hE : E k r = (N : Int))
    (hcone : InACone k r ∨ InDCone k r) :
    (k, r) ∈ atomBox N := by
  -- proof by cases on the cone
  -- A-cone: use `Q = 2E` and nonnegativity to get `0 <= k,r` and upper bounds.
  -- D-cone: write `u=-k-1`, `v=-r-1`; use the D-cone positive formula.
  -- Finish with `simp [atomBox, coeffRange, coeffBound]` and `omega`.
  sorry
```

The final project cannot contain `sorry`, of course.  The skeleton above is just the theorem to target.  The proof is straightforward but a little long.  I would prove it in smaller lemmas.

### A-cone bound

For the A-cone, use `Q_eq_two_mul_E` rather than unfolding `triZ`.

If

```text
0 <= k, 0 <= r, E(k,r)=N,
```

then

```text
Q(k,r)=2N.
```

In the A-cone all terms in

```text
Q(k,r) = 4k^2 + 2k + r^2 + (6k+1)r
```

are nonnegative.  In particular,

```text
2k <= Q(k,r) = 2N,
r  <= Q(k,r) = 2N.
```

So

```text
0 <= k <= N <= 2N+1,
0 <= r <= 2N <= 2N+1.
```

A useful theorem shape is:

```lean
theorem A_atom_bounds {N : Nat} {k r : Int}
    (hA : InACone k r) (hE : E k r = (N : Int)) :
    -(coeffBound N) <= k ∧ k <= coeffBound N ∧
    -(coeffBound N) <= r ∧ r <= coeffBound N := by
  rcases hA with ⟨hk0, hr0⟩
  have hQ : Q k r = 2 * (N : Int) := by
    rw [Q_eq_two_mul_E, hE]
  unfold Q at hQ
  -- all terms are nonnegative; derive coarse upper bounds
  have hkr0 : 0 <= k * r := mul_nonneg hk0 hr0
  have h6kr0 : 0 <= 6 * k * r := by nlinarith
  have hk_upper : k <= (N : Int) := by
    nlinarith [sq_nonneg k, sq_nonneg r, h6kr0, hk0, hr0, hQ]
  have hr_upper : r <= 2 * (N : Int) := by
    nlinarith [sq_nonneg k, sq_nonneg r, h6kr0, hk0, hr0, hQ]
  unfold coeffBound
  omega
```

Depending on how `nlinarith` sees the term `(6*k+1)*r`, you may need the extra identity

```lean
have hterm : (6 * k + 1) * r = 6 * k * r + r := by ring
```

and rewrite `hQ` with it before the `nlinarith` calls.

### D-cone bound

For the D-cone, do not reason directly with negative variables.  Use

```text
k = -u - 1,
r = -v - 1,
u,v >= 0.
```

Then

```text
Q(-u-1,-v-1) = 4u^2 + 12u + 6uv + v^2 + 7v + 8.
```

Since `Q = 2N`, this gives

```text
12u <= 2N,
7v <= 2N,
```

hence certainly

```text
u <= 2N,
v <= 2N.
```

Therefore

```text
k = -u-1 >= -(2N+1),
r = -v-1 >= -(2N+1),
```

and the upper bounds `k <= 2N+1`, `r <= 2N+1` are trivial because `k,r < 0`.

Add this lemma:

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

/-- D-cone doubled exponent after `k=-u-1`, `r=-v-1`. -/
theorem Q_neg_succ_neg_succ (u v : Int) :
    Q (-u - 1) (-v - 1) =
      4 * u ^ 2 + 12 * u + 6 * u * v + v ^ 2 + 7 * v + 8 := by
  unfold Q
  ring

end Ch10
end QseriesFormalization
```

Then prove a D-bound lemma using `u = -k - 1`, `v = -r - 1`.

```lean
theorem D_atom_bounds {N : Nat} {k r : Int}
    (hD : InDCone k r) (hE : E k r = (N : Int)) :
    -(coeffBound N) <= k ∧ k <= coeffBound N ∧
    -(coeffBound N) <= r ∧ r <= coeffBound N := by
  rcases hD with ⟨hkneg, hrneg⟩
  let u : Int := -k - 1
  let v : Int := -r - 1
  have hu0 : 0 <= u := by omega
  have hv0 : 0 <= v := by omega
  have hk_eq : k = -u - 1 := by omega
  have hr_eq : r = -v - 1 := by omega
  have hQ : Q k r = 2 * (N : Int) := by
    rw [Q_eq_two_mul_E, hE]
  have hQ_uv :
      4 * u ^ 2 + 12 * u + 6 * u * v + v ^ 2 + 7 * v + 8 = 2 * (N : Int) := by
    rw [← Q_neg_succ_neg_succ u v]
    rw [← hk_eq, ← hr_eq]
    exact hQ
  have huv0 : 0 <= u * v := mul_nonneg hu0 hv0
  have hu_upper : u <= 2 * (N : Int) := by
    nlinarith [sq_nonneg u, sq_nonneg v, huv0, hu0, hv0, hQ_uv]
  have hv_upper : v <= 2 * (N : Int) := by
    nlinarith [sq_nonneg u, sq_nonneg v, huv0, hu0, hv0, hQ_uv]
  unfold coeffBound
  omega
```

If this exact proof needs small tuning, the structure is still the right one.  The point is that the D-cone bound should be proved in positive variables.

### From bounds to box membership

Once A/D bounds are proven, box membership is mechanical:

```lean
theorem activeAtom_mem_atomBox {N : Nat} {k r : Int}
    (hE : E k r = (N : Int))
    (hcone : InACone k r ∨ InDCone k r) :
    (k, r) ∈ atomBox N := by
  have hbounds := by
    rcases hcone with hA | hD
    · exact A_atom_bounds hA hE
    · exact D_atom_bounds hD hE
  rcases hbounds with ⟨hklo, hkhi, hrlo, hrhi⟩
  simp [atomBox, coeffRange, coeffBound, hklo, hkhi, hrlo, hrhi]
```

This theorem is the mathematical justification for the finite-box definition.

## Should Theorem 5 be a theorem or a definition?

It depends on what you mean by `B`.

### If `B` is introduced as this cone series

Then Theorem 5 should be a **definition plus simp theorem**:

```lean
def Bcoeff (N : Nat) : Int := ...

theorem Bcoeff_eq_sum (N : Nat) :
    Bcoeff N = ... := rfl
```

This is enough.  Do not waste effort proving a theorem that just unfolds the definition.

### If `B` already exists as a formal `PowerSeries`

Then Theorem 5 is a real bridge theorem:

```text
coefficient of the formal series B at N = finite cone sum at N.
```

In that case, still define `Bcoeff` first, then define the series from coefficients:

```lean
-- schematic, depending on your existing q-series infrastructure
noncomputable def BSeries : PowerSeries Int :=
  PowerSeries.mk Bcoeff

@[simp] theorem coeff_BSeries (N : Nat) :
    PowerSeries.coeff Int N BSeries = Bcoeff N := rfl
```

If your existing infrastructure has its own series constructor, adapt this pattern.  The coefficient function should remain the primary object.

## Why not `Finsupp` first?

`Finsupp` is attractive only after you have already proved finite support.  Here, proving finite support is exactly the work.  If you start with `Finsupp`, Lean will ask for the same bounds plus extra support bookkeeping.

The explicit `Finset.Icc` box is simpler:

```text
finite by construction,
computable,
easy to inspect,
works with `norm_num`, `decide`, and `native_decide`,
works immediately for B_1, B_3, B_34.
```

You can always wrap it in a `Finsupp` later if some downstream theorem wants a finitely supported function.

## Why not `PowerSeries` first?

For this theorem, `PowerSeries` is not the hard part.  The hard part is coefficient extraction from an indefinite cone.  Define the coefficients first; then make the power series as a wrapper.

Recommended order:

```text
1. Define `Bcoeff : Nat -> Int` by finite box.
2. Prove support-bound theorem for mathematical correctness.
3. Prove small coefficients and nonmultiplicativity from `Bcoeff`.
4. Define `BSeries` from `Bcoeff` only when needed.
5. Prove product/factorization identities later using coefficient extensionality.
```

## Recommended final API

The coefficient file should expose these names:

```lean
def coeffBound (N : Nat) : Int

def coeffRange (N : Nat) : Finset Int

def atomBox (N : Nat) : Finset (Int × Int)

def activeAtom (N : Nat) (p : Int × Int) : Prop

def atomFinset (N : Nat) : Finset (Int × Int)

def Bcoeff (N : Nat) : Int

theorem mem_atomFinset_iff (N : Nat) (p : Int × Int) :
  p ∈ atomFinset N ↔
    p ∈ atomBox N ∧ E p.1 p.2 = (N : Int) ∧
      (InACone p.1 p.2 ∨ InDCone p.1 p.2)

theorem activeAtom_mem_atomBox {N : Nat} {k r : Int} :
  E k r = (N : Int) ->
  InACone k r ∨ InDCone k r ->
  (k, r) ∈ atomBox N

theorem Bcoeff_eq_sum (N : Nat) :
  Bcoeff N = (atomFinset N).sum (fun p => BWeight p.1 p.2)
```

Then later, if you want the beta/norm form:

```lean
def betaAtomFinset (N : Nat) : Finset PhiInt :=
  (atomFinset N).image ⟨fun p => beta p.1 p.2, beta_injective_on_pairs⟩
```

But do not start there.  Start with `(k,r)` atoms.

## Is Theorem 5 worth formalizing?

As a standalone theorem, only partly.

If `Bcoeff` is defined as the finite sum, then

```text
Theorem 5 is mostly definitional.
```

The theorems that are actually worth formalizing are:

1. `activeAtom_mem_atomBox`: the finite box is large enough.
2. `Bcoeff_eq_sum`: a simp/rfl theorem giving the coefficient API.
3. Small coefficient theorems, such as `Bcoeff 1 = 1`, `Bcoeff 3 = -2`, `Bcoeff 34 = 3`.
4. The beta/norm reindexing theorem, if you want the norm-support theorem to refer directly to coefficients.
5. A future bridge theorem from the existing q-series/PowerSeries object to `Bcoeff`.

So I would include Theorem 5 in the paper-facing API, but internally I would make it a definition plus a support-bound theorem.

## Bottom line

The path of least resistance in Mathlib 4.30.0 is:

```text
Define `Bcoeff` by a finite `Finset.Icc` rectangle with bound `2N+1`,
filter by `E=N` and active same-sign cone membership,
sum `BWeight`,
prove a separate support-bound theorem,
postpone `Finsupp` and `PowerSeries` wrappers.
```

This gives you a computable coefficient function immediately, works with your existing small coefficient proofs, and keeps the genuinely difficult q-series identities out of the core algebra layer.
