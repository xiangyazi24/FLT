# Q2638 (dm-codex1): adversarial audit of `EulerSquarePairDescent`

Target repo path mentioned by requester: `/Users/huangx/repos/flt-ai`  
Target Lean file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`

This audit is only about `EulerSquarePairDescent`.  I am not discussing the already-checked AP-to-Euler construction.

## Verdict

The route described is mathematically sound, provided the implementation really has the following two non-negotiable points:

1. `F.A` is the **half common factor** `a` from `k = 2*a`, not the original common refinement factor `k`.
2. `Even a` is proved from the balance equation, not from the original parity of `U` and `Up` alone.

Under those conventions the descended object

```lean
F.A = a
F.D = d
F.B = b
F.C = c
```

is the right smaller `EulerSquarePair`, and the square extraction orientation

```lean
M = 4*a^2 + d^2 = c^2
N = 16*a^2 + d^2 = b^2
```

matches the fields `C = c` and `B = b`.

## 1. Descent target: `F.A * F.D < E.A * E.D`

The target is exactly the interface currently stated by the file:

```lean
def EulerSquarePairDescent : Prop :=
  ∀ E : EulerSquarePair, ∃ F : EulerSquarePair, F.A * F.D < E.A * E.D
```

So proving

```lean
a * d < E.A * E.D
```

is sufficient because the constructed `F` has `F.A = a` and `F.D = d`.

This is also mathematically adequate for infinite descent, as long as the downstream contradiction uses the positive integer measure `A*D`.  Every `EulerSquarePair` has `0 < A` and `0 < D`, hence `0 < A*D`, so a strict descent in `A*D` transfers to a strict descent in the corresponding natural measure.

In fact, the implementation can prove a slightly stronger intermediate inequality:

```lean
a * d < E.A
```

because

```lean
E.A = U * V = (2*a*b) * (c*d) = 2*a*b*c*d
```

and `a,b,c,d` are all positive.  Since `0 < E.D`, over integers we have `1 ≤ E.D`, so

```lean
E.A ≤ E.A * E.D
```

and therefore

```lean
a * d < E.A * E.D.
```

A very Lean-friendly proof is to factor directly:

```lean
E.A * E.D = (a*d) * (2*b*c*E.D)
```

and prove `1 < 2*b*c*E.D` from `0 < b`, `0 < c`, and `0 < E.D`.  But I would still expose the stronger `a*d < E.A` as a small helper, because it isolates the descent arithmetic from the `D` multiplier.

There is no need to change the interface to `< E.A`.  If a later theorem wants descent by `E.A` specifically, this construction can also give it, but the hard interface you quoted is product descent.

## 2. No circularity in `even_of_descent_balance`

Using

```lean
even_of_descent_balance
```

before square extraction is not circular, provided its inputs are only:

```lean
Odd b
Odd c
Odd d
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2)
```

The parity argument is independent of `square_factor_balance_int` and independent of the construction of `F`.

Modulo `8`, odd squares are `1`.  Thus the balance equation gives

```text
1 * (4*a^2 + 1) ≡ 1 * (16*a^2 + 1)  (mod 8)
```

so

```text
4*a^2 + 1 ≡ 1  (mod 8),
```

hence `4*a^2 ≡ 0 (mod 8)`.  If `a` were odd then `a^2 ≡ 1 (mod 8)`, giving `4*a^2 ≡ 4 (mod 8)`, contradiction.  Therefore `Even a`.

This proof uses only the refinement balance equation and oddness of `b,c,d`.  It does not depend on knowing that either cofactor is a square.  So there is no circularity.

One implementation caveat: if your proof of `even_of_descent_balance` internally calls `square_factor_balance_int`, then it is not the direct parity lemma described above.  That would not be a mathematical circularity in the final theorem, but it would make the dependency DAG less clean.  The clean version is the direct mod-`8` proof.

## 3. Cofactor orientation and square-factor balance

The orientation described is correct.

You have the balance equation in the form

```lean
hbal : b^2 * M = c^2 * N
```

where

```lean
M = 4*a^2 + d^2
N = 16*a^2 + d^2
```

The checked theorem

```lean
square_factor_balance_int
  (hb hc hM hN : positives)
  (hbc : IsCoprime b c)
  (hMN : IsCoprime M N)
  (h : b^2*M = c^2*N) : M = c^2 ∧ N = b^2
```

then gives exactly

```lean
4*a^2 + d^2 = c^2
16*a^2 + d^2 = b^2
```

which are the required equations for

```lean
F.C = c
F.B = b
```

because `EulerSquarePair` expects

```lean
hB : B^2 = 16*A^2 + D^2
hC : C^2 = 4*A^2 + D^2
```

So there is no `b/c` swap if the equation is passed to `square_factor_balance_int` as

```lean
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2)
```

Do not commute or symmetrize the balance equation itself before applying `square_factor_balance_int`.  The only likely `.symm` needed is for the coprimality theorem if its local statement returns

```lean
IsCoprime (16*a^2 + d^2) (4*a^2 + d^2)
```

but the balance theorem wants

```lean
IsCoprime (4*a^2 + d^2) (16*a^2 + d^2).
```

That `.symm` is harmless.  Swapping `M` and `N` in the balance theorem is not harmless.

## 4. Nat refinement wrapper via `natAbs`

There is no mathematical issue with wrapping the Nat refinement through `natAbs`, because all four inputs are strictly positive integers:

```lean
0 < U, 0 < V, 0 < Up, 0 < Vp
```

The wrapper should prove, once and for all:

```lean
(U.natAbs : ℤ) = U
(V.natAbs : ℤ) = V
(Up.natAbs : ℤ) = Up
(Vp.natAbs : ℤ) = Vp
```

Then the product equality transfers cleanly:

```lean
U * V = Up * Vp
```

to

```lean
U.natAbs * V.natAbs = Up.natAbs * Vp.natAbs
```

using `Int.natAbs_mul` or by casting back to `ℤ` after positivity normalization.

Likewise, the coprimality transfer is sign-safe because there are no negative representatives left.  The returned Nat factors can be cast back to positive integers, giving positive `k,b,c,d`.

The implementation detail to watch is not the math; it is simplification control.  I would keep all `toNat`/`natAbs` casts inside `two_coprime_factorizations_refine_int_pos`, and never let them leak into the main descent proof.

## 5. Hidden weaknesses to check before trusting the final theorem

The route is sound, but these are the places I would inspect adversarially in the Lean code.

### 5.1 `IsCoprime a d` must be derived from `IsCoprime k d`

The Nat/Int refinement gives pairwise coprimality for `k,b,c,d`, not automatically for the half-factor `a`.

After proving

```lean
k = 2*a
```

you still need a lemma of the form:

```lean
private lemma coprime_of_coprime_two_mul_left {a d : ℤ}
    (h : IsCoprime (2 * a) d) : IsCoprime a d := by
  -- divisibility/gcd/Bézout proof, depending on the local IsCoprime API
  sorry
```

This does not require `Odd d`; any common divisor of `a` and `d` is a common divisor of `2*a` and `d`.

### 5.2 `Even a` cannot come from refinement parity alone

The false inference would be:

```lean
Even U
U = k*b
Odd b
k = 2*a
-- therefore Even a
```

This is false.  Example: `a=1`, `k=2`, `b=1`.

So the implementation should contain no lemma that tries to prove `Even a` from `Even k` or from both `U` and `Up` being even.  The first valid proof of `Even a` is the mod-`8` balance proof.

### 5.3 The signed-orientation branch should collapse immediately

From `signed_even_odd_params_same_orientation E`, there are two cases:

```lean
E.D  = U^2 - V^2 ∧ E.D  = 4*Up^2 - Vp^2
-D   = U^2 - V^2 ∧ -D   = 4*Up^2 - Vp^2
```

Both imply the same equality:

```lean
U^2 - V^2 = 4*Up^2 - Vp^2
```

The proof should convert both branches to this common equality or to a common call of `refinement_equation_of_same_orientation`.  Do not duplicate the full descent after the branch.

If `refinement_equation_of_same_orientation` is parameterized by a signed `D`, instantiate it with `E.D` in the positive branch and with `-E.D` in the negative branch.

### 5.4 Cofactor coprimality must not rely on an already constructed `F`

You said `euler_cofactor_coprime` gives cofactor coprimality from `Odd d` and `IsCoprime a d`.  That is exactly what is needed.

But if the local theorem is instead a method that requires an existing `EulerSquarePair`, then using it here would be circular because constructing that `EulerSquarePair` requires the cofactor equations and `Even a`.  The safe shape is a standalone lemma like:

```lean
private lemma euler_cofactor_coprime_core
    {a d : ℤ}
    (hodd : Odd d)
    (hcop : IsCoprime a d) :
    IsCoprime (16*a^2 + d^2) (4*a^2 + d^2) := by
  ...
```

Then use `.symm` if `square_factor_balance_int` wants the opposite order.

### 5.5 Positivity of the cofactors should come only from `0 < d`

For `square_factor_balance_int`, the cofactor positivity assumptions can be proved without knowing anything about `a`:

```lean
0 < 4*a^2 + d^2
0 < 16*a^2 + d^2
```

because `0 < d`, hence `0 < d^2`, and `a^2 ≥ 0`.

This is useful because it avoids accidentally depending on later square extraction or on `Even a`.

### 5.6 Strict descent should use integer positivity carefully

Over `ℤ`, from `0 < E.D` you need either `have hEDge : 1 ≤ E.D := by omega` or a direct positive-factor proof.

A robust proof shape is:

```lean
have hEA : E.A = 2 * a * b * c * d := by
  -- from E.A = U*V, U=2*a*b, V=c*d
  ring_nf at *

have hsmallEA : a * d < E.A := by
  rw [hEA]
  -- all factors positive; equivalently `1 < 2*b*c`
  nlinarith [hapos, hbpos, hcpos, hdpos]

have hEApos : 0 < E.A := E.hA
have hEDge : 1 ≤ E.D := by omega
have hEA_le_mul : E.A ≤ E.A * E.D := by
  nlinarith

exact lt_of_lt_of_le hsmallEA hEA_le_mul
```

Or prove the direct factorization:

```lean
E.A * E.D = (a*d) * (2*b*c*E.D)
```

and show `1 < 2*b*c*E.D`.

## 6. Lean-facing helper skeleton

The following is not meant to replace the implementation you already have; it records the auxiliary shapes I would expect to see.  The imports are included so this can be pasted into a Lean-facing note or scratch file.

```lean
import FLT.Assumptions.MazurProof.N12EulerAux
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private theorem two_coprime_factorizations_refine_int_pos
    {U V Up Vp : ℤ}
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hUppos : 0 < Up) (hVppos : 0 < Vp)
    (hUV : IsCoprime U V)
    (hUpVp : IsCoprime Up Vp)
    (hprod : U * V = Up * Vp) :
    ∃ k b c d : ℤ,
      0 < k ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      U = k * b ∧ V = c * d ∧ Up = k * c ∧ Vp = b * d ∧
      IsCoprime k b ∧ IsCoprime k c ∧ IsCoprime k d ∧
      IsCoprime b c ∧ IsCoprime b d ∧ IsCoprime c d := by
  -- wrapper around `two_coprime_factorizations_refine_nat`
  -- keep all `natAbs`/`toNat` casts confined here
  sorry

private lemma odd_factors_of_odd_mul_int {x y : ℤ}
    (hxy : Odd (x * y)) : Odd x ∧ Odd y := by
  sorry

private lemma even_left_of_even_mul_odd_int {x y : ℤ}
    (hxy : Even (x * y)) (hy : Odd y) : Even x := by
  sorry

private lemma even_pos_as_two_mul {k : ℤ}
    (hkpos : 0 < k) (hkeven : Even k) :
    ∃ a : ℤ, 0 < a ∧ k = 2 * a := by
  rcases hkeven with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · nlinarith
  · nlinarith

private lemma coprime_of_coprime_two_mul_left {a d : ℤ}
    (h : IsCoprime (2 * a) d) : IsCoprime a d := by
  sorry

private lemma pos_four_sq_add_sq_of_pos_right {a d : ℤ}
    (hdpos : 0 < d) : 0 < 4 * a ^ 2 + d ^ 2 := by
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdsq : 0 < d ^ 2 := sq_pos_of_ne_zero hdne
  have hasq : 0 ≤ a ^ 2 := sq_nonneg a
  nlinarith

private lemma pos_sixteen_sq_add_sq_of_pos_right {a d : ℤ}
    (hdpos : 0 < d) : 0 < 16 * a ^ 2 + d ^ 2 := by
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdsq : 0 < d ^ 2 := sq_pos_of_ne_zero hdne
  have hasq : 0 ≤ a ^ 2 := sq_nonneg a
  nlinarith

private lemma even_of_descent_balance
    {a b c d : ℤ}
    (hbodd : Odd b) (hcodd : Odd c) (hdodd : Odd d)
    (hbal : b ^ 2 * (4 * a ^ 2 + d ^ 2)
          = c ^ 2 * (16 * a ^ 2 + d ^ 2)) :
    Even a := by
  -- Direct mod-8 proof.  Do not call `square_factor_balance_int` here.
  sorry

private lemma descent_product_lt_of_refinement
    {E_A E_D a b c d : ℤ}
    (hEA : E_A = 2 * a * b * c * d)
    (hapos : 0 < a) (hbpos : 0 < b) (hcpos : 0 < c) (hdpos : 0 < d)
    (hEDpos : 0 < E_D) :
    a * d < E_A * E_D := by
  have hsmallEA : a * d < E_A := by
    rw [hEA]
    nlinarith
  have hEApos : 0 < E_A := by
    rw [hEA]
    nlinarith
  have hEDge : 1 ≤ E_D := by omega
  have hEAle : E_A ≤ E_A * E_D := by
    nlinarith
  exact lt_of_lt_of_le hsmallEA hEAle

end MazurProof.RationalPointsN12
```

## 7. Validation commands I would run

From the local checkout:

```bash
cd /Users/huangx/repos/flt-ai

# Fast single-file check of the target implementation.
lake env lean FLT/Assumptions/MazurProof/N12FourSquaresAP.lean

# Check the auxiliary file that provides square_factor_balance_int.
lake env lean FLT/Assumptions/MazurProof/N12EulerAux.lean

# Module-level build checks, if the package exposes these module names.
lake build FLT.Assumptions.MazurProof.N12EulerAux
lake build FLT.Assumptions.MazurProof.N12FourSquaresAP

# Whole-project check if the single-file/module checks pass.
lake build

# Audit that the constructive theorem and its wrappers did not introduce new placeholders.
rg -n "sorry|admit|axiom|set_option autoImplicit true" \
  FLT/Assumptions/MazurProof/N12FourSquaresAP.lean \
  FLT/Assumptions/MazurProof/N12EulerAux.lean

# Optional: check exactly what changed before committing.
git diff -- FLT/Assumptions/MazurProof/N12FourSquaresAP.lean \
             FLT/Assumptions/MazurProof/N12EulerAux.lean
git diff --check
```

## Final audit answer

I would treat the implementation as sound if it typechecks and the direct inspection confirms:

* `a` is introduced by `k = 2*a` and `F.A = a`.
* `Even a` is proved by the direct mod-`8` balance lemma, not by refinement parity alone.
* `IsCoprime a d` is explicitly derived from the refinement coprimality for `k` and `d`.
* `square_factor_balance_int` is applied with `M = 4*a^2+d^2`, `N = 16*a^2+d^2`, and the balance equation in the order `b^2*M = c^2*N`.
* The signed-orientation branch is collapsed to the common balance equation before the rest of the descent.
* The descent inequality proves `F.A*F.D = a*d < E.A*E.D`, preferably via the stronger intermediate `a*d < E.A`.

No correction to the mathematical construction is needed under those conditions.
