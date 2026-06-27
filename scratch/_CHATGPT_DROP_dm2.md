# Q1073 (dm2): shortest Lean path for `weil_pairing_gives_primitive_root`

## Executive answer

For the theorem

```lean
theorem weil_pairing_gives_primitive_root
    (E : WeierstrassCurve Rat) [E.IsElliptic] {m : Nat}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    Exists fun zeta : Rat => IsPrimitiveRoot zeta m
```

the important point is this:

For `m >= 3`, the conclusion is false over `Rat`, by the already available theorem you mentioned:

```lean
isPrimitiveRoot_rat_order_le_two
```

So the `m >= 3` branch should not try to construct a rational primitive root. It should prove `False` from `hfull`, then close by `False.elim`.

The shortest Lean path is therefore **not** to formalize the full Weil pairing. It is to isolate the hard geometric input as the smallest possible local lemma:

```lean
not_hasFullRationalTorsion_of_three_le
```

or equivalently:

```lean
HasFullRationalTorsion E m -> False, when 3 <= m.
```

Then the target theorem is just the existing `m = 1`, `m = 2` proofs plus an `omega` case split.

This is the shortest project path because every alternative route still needs the same missing theorem in disguise:

```text
full rational m-torsion over Q forces mu_m over Q.
```

That statement is usually proved by the Weil pairing. The determinant route packages the same content as

```text
det rho_m = cyclotomic character.
```

It avoids spelling out divisors and Weil-pairing algebra in the target file, but proving the determinant theorem itself is essentially the Weil-pairing theorem.

---

## 1. Determinant of the mod-m Galois representation

Mathematically, the determinant route is valid:

```text
rho_m : Gal(Qbar / Q) -> GL_2(ZMod m)
det rho_m = chi_m
```

where `chi_m` is the mod-`m` cyclotomic character. If all `m`-torsion points are rational, the Galois action on `E[m]` is trivial, so `rho_m` is trivial, hence `det rho_m` is trivial, hence `chi_m` is trivial. For `Q`, triviality of `chi_m` means all `m`th roots of unity are rational, so in particular there is a rational primitive `m`th root of unity. For `m >= 3`, this contradicts `isPrimitiveRoot_rat_order_le_two`.

But in Lean, this is only shorter if you already have the determinant theorem as a theorem. The following pieces are needed:

```text
A. A usable type for E[m] over an algebraic closure.
B. A Galois action on E[m].
C. A proof that `hfull` makes that action trivial.
D. A representation matrix after choosing a basis.
E. A determinant of that representation.
F. The theorem `det rho_m = cyclotomic_character m`.
G. Nontriviality of the cyclotomic character over Q for m >= 3,
   or a bridge from trivial cyclotomic character to a rational primitive root.
```

The prompt says FLT has:

```text
WeierstrassCurve.galoisRep
WeierstrassCurve.nTorsion
IsPrimitiveRoot.autToPow
```

Those names are useful, but they do not by themselves give item F. The determinant identity is the serious theorem. In standard mathematics it is proved from the Weil pairing: Galois equivariance of the pairing gives

```text
e_m(sigma P, sigma Q) = sigma(e_m(P, Q)),
```

and if the matrix of `sigma` on a basis `(P, Q)` has determinant `d`, then

```text
e_m(sigma P, sigma Q) = e_m(P, Q)^d.
```

Comparing both sides identifies `d` with the cyclotomic character. Thus the determinant theorem is not an independent easy alternative; it is the Weil-pairing argument in determinant form.

### Lean recommendation for the determinant route

If you want to keep the target file clean and postpone the geometry, introduce a single black-box theorem with the determinant/cyclotomic content, not the full Weil pairing API.

A good interface is:

```lean
import Mathlib

/-
Schematic interface. Use the actual FLT namespaces and definitions.
The point is the shape of the hard lemma, not these placeholder names.
-/

namespace FLT

open scoped BigOperators

-- Hard theorem, eventually proved by either Weil pairing or determinant machinery.
axiom no_full_rational_torsion_of_three_le
    (E : WeierstrassCurve Rat) [E.IsElliptic] {m : Nat}
    (hm3 : 3 <= m) :
    Not (HasFullRationalTorsion E m)

end FLT
```

This is better than exposing all of the Weil-pairing details in the final theorem.

If you specifically want the determinant package, the minimal hard theorem can instead be phrased as:

```lean
import Mathlib

/-
Schematic only. The names `CyclotomicCharMod` and `galoisRepDet_eq_cyclotomic`
stand for whatever representation API FLT actually uses.
-/

namespace FLT

open scoped BigOperators

-- Hard theorem: determinant of the mod-m Galois representation is cyclotomic.
axiom galoisRepDet_eq_cyclotomic
    (E : WeierstrassCurve Rat) [E.IsElliptic] (m : Nat) :
    True

-- Hard theorem or number-theory bridge: over Q the cyclotomic character is nontrivial
-- when m >= 3.
axiom cyclotomic_character_nontrivial_of_three_le
    {m : Nat} (hm3 : 3 <= m) :
    True

end FLT
```

But this is not really fewer mathematical obligations than `no_full_rational_torsion_of_three_le`; it just splits the obligation into representation theory plus cyclotomic character facts.

---

## 2. Direct structure of `E(Q)_tors`

This is not a short route in Mathlib.

From

```lean
HasFullRationalTorsion E m
```

where

```lean
Exists fun f : ZMod m x ZMod m ->+ (E/Q).Point => Function.Injective f
```

you get at least `m^2` rational torsion points of exponent dividing `m`. For `m >= 3`, this is at least nine points.

But that cardinality fact alone is not contradictory.

Examples of why cardinality is too weak:

```text
m = 3:  m^2 = 9, and Mazur's theorem allows cyclic rational torsion of order 9.
m = 4:  m^2 = 16, and Mazur's theorem allows rational torsion of order 16 in some cases.
```

The problem is not merely the number of torsion points; it is the existence of a subgroup isomorphic to

```text
Z/mZ x Z/mZ.
```

To rule that out directly, you need a classification of rational torsion on elliptic curves over `Q`, essentially Mazur's torsion theorem or enough of it to exclude full level `m >= 3`. That is far heavier than the Weil pairing consequence.

Finiteness of `E(Q)_tors` also does not help. It only says the torsion subgroup is finite. It gives no contradiction with a finite subgroup of order `m^2`.

A finite-cardinality approach would need one of the following deep inputs:

```text
- Mazur torsion classification over Q;
- a strong enough structure theorem excluding Z/mZ x Z/mZ for m >= 3;
- a modular-curve theorem about rational full-level structures.
```

All of these are much larger formalization projects than the Weil-pairing/determinant consequence.

---

## 3. Purely number-theoretic routes

Kronecker-Weber and Neron-Ogg-Shafarevich do not by themselves solve the problem.

Kronecker-Weber says finite abelian extensions of `Q` sit in cyclotomic extensions. But the needed implication is the opposite kind of statement:

```text
Q(E[m]) contains Q(mu_m).
```

That inclusion is exactly the Weil-pairing theorem, or equivalently the determinant identity for the mod-`m` Galois representation.

Neron-Ogg-Shafarevich controls ramification of torsion fields at primes of good reduction. But if `E[m]` is rational, then `Q(E[m]) = Q`, which is already unramified everywhere. There is no contradiction unless you also know that `Q(mu_m)` is contained in `Q(E[m])`, and that containment is again the Weil-pairing/determinant input.

Reduction modulo primes also does not give a uniform short proof. For each good prime `p` not dividing `m`, rational full `m`-torsion would imply

```text
m^2 divides #E(F_p).
```

For a fixed curve, enough reductions can often prove contradictions computationally. But the theorem is uniform in `E`, so this route would require serious global input about all elliptic curves over `Q`. That is not shorter.

---

## 4. How to use the FLT declarations you mentioned

The declarations

```text
WeierstrassCurve.galoisRep
WeierstrassCurve.nTorsion
IsPrimitiveRoot.autToPow
```

can be part of a determinant route, but only after adding the missing determinant theorem.

A possible dependency chain is:

```text
hfull
  -> choose two rational independent m-torsion points P,Q
  -> identify them as a basis of geometric E[m]
  -> Galois acts trivially on that basis
  -> rho_m(sigma) = 1
  -> det rho_m(sigma) = 1
  -> by det rho_m = cyclotomic character, chi_m(sigma) = 1
  -> cyclotomic character is trivial
  -> primitive m-th root of unity is rational
  -> contradiction for m >= 3 over Rat
```

The two genuinely hard Lean steps are:

```text
1. `det rho_m = cyclotomic character`.
2. `cyclotomic character trivial over Q -> exists zeta : Rat, IsPrimitiveRoot zeta m`,
   or equivalently nontriviality of the cyclotomic character for m >= 3.
```

`IsPrimitiveRoot.autToPow` helps with the second step only after you have a primitive root in some extension and enough Galois/cyclotomic field infrastructure to talk about its automorphisms. It does not prove the determinant formula, and it does not by itself show that the cyclotomic character has nontrivial image over `Q`.

So, for FLT, I would not try to wire these together inside the proof of `weil_pairing_gives_primitive_root`. Put the hard representation theorem behind a small interface.

---

## Recommended shortest implementation shape

Since the `m = 1` and `m = 2` cases are already handled, the final theorem should look like this:

```lean
import Mathlib

/-
Schematic proof shape. Replace lemma names with the actual FLT names.
This assumes the project already has:

  primitiveRoot_rat_one : Exists fun zeta : Rat => IsPrimitiveRoot zeta 1
  primitiveRoot_rat_two : Exists fun zeta : Rat => IsPrimitiveRoot zeta 2

and adds the one hard geometric input:

  no_full_rational_torsion_of_three_le
-/

namespace FLT

open scoped BigOperators

-- This is the single hard input. Prove it later using Weil pairing or determinant.
axiom no_full_rational_torsion_of_three_le
    (E : WeierstrassCurve Rat) [E.IsElliptic] {m : Nat}
    (hm3 : 3 <= m) :
    Not (HasFullRationalTorsion E m)

-- Existing small-case lemmas, names schematic.
axiom primitiveRoot_rat_one :
    Exists fun zeta : Rat => IsPrimitiveRoot zeta 1

axiom primitiveRoot_rat_two :
    Exists fun zeta : Rat => IsPrimitiveRoot zeta 2

-- Target proof skeleton.
theorem weil_pairing_gives_primitive_root_skeleton
    (E : WeierstrassCurve Rat) [E.IsElliptic] {m : Nat}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    Exists fun zeta : Rat => IsPrimitiveRoot zeta m := by
  have hcases : m = 1 / m = 2 / 3 <= m := by
    omega
  rcases hcases with h1 | h2_or_ge3
  · subst m
    exact primitiveRoot_rat_one
  · rcases h2_or_ge3 with h2 | hm3
    · subst m
      exact primitiveRoot_rat_two
    · exact False.elim ((no_full_rational_torsion_of_three_le E hm3) hfull)

end FLT
```

This is the best proof shape for the theorem itself.

If you want the hard lemma to remember its mathematical source, name it after the determinant/cyclotomic consequence:

```lean
import Mathlib

namespace FLT

open scoped BigOperators

/--
Full rational m-torsion over Q forces a rational primitive m-th root of unity.
Mathematical proof: Weil pairing, or equivalently det rho_m = cyclotomic character.
-/
axiom full_rational_torsion_forces_rat_primitive_root
    (E : WeierstrassCurve Rat) [E.IsElliptic] {m : Nat}
    (hm : 0 < m) :
    HasFullRationalTorsion E m ->
      Exists fun zeta : Rat => IsPrimitiveRoot zeta m

end FLT
```

But this second axiom is almost the original theorem, so I prefer the negative lemma:

```lean
no_full_rational_torsion_of_three_le
```

It cleanly expresses the only branch where a hard theorem is needed, while leaving the solved `m = 1` and `m = 2` branches constructive.

---

## Why this is better than carrying a fake primitive root construction

In the `m >= 3` branch, the theorem is vacuous. Therefore the proof term should be vacuous:

```lean
exact False.elim hcontradiction
```

Trying to actually produce a `zeta : Rat` in that branch makes the Lean goal harder than necessary. It forces you to formalize a bridge from cyclotomic-character triviality to a rational root of unity, only to immediately contradict `isPrimitiveRoot_rat_order_le_two`.

Instead, prove directly:

```lean
hfull : HasFullRationalTorsion E m
hm3   : 3 <= m
----------------
False
```

That is the right local shape.

---

## Final recommendation

The shortest proof path in Lean 4 / Mathlib for FLT is:

1. Keep the completed `m = 1` and `m = 2` branches.
2. Add one hard lemma:

   ```lean
   no_full_rational_torsion_of_three_le
       (E : WeierstrassCurve Rat) [E.IsElliptic] {m : Nat}
       (hm3 : 3 <= m) :
       Not (HasFullRationalTorsion E m)
   ```

3. Prove the target theorem by `omega` case split and `False.elim` in the `m >= 3` branch.
4. Later prove `no_full_rational_torsion_of_three_le` using either:

   ```text
   Weil pairing nondegeneracy + Galois equivariance
   ```

   or the equivalent packaged theorem

   ```text
   det(galoisRep E m) = cyclotomic character mod m.
   ```

Do not try to use finiteness of torsion, Kronecker-Weber, or Neron-Ogg-Shafarevich as a shortcut. They do not give the needed implication without the same Weil-pairing/determinant input.

So the practical answer is:

```text
Use the determinant route only as an interface theorem.
Do not attempt to prove determinant = cyclotomic from current low-level Mathlib pieces unless you are ready to formalize the Weil pairing argument anyway.
For the target theorem, the shortest Lean proof is a negative `m >= 3` lemma plus the already-finished `m = 1,2` cases.
```
