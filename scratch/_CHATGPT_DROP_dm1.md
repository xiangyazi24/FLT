# Q1993 (dm1): `DescentObstructionN16.lean`

Below is a complete Lean 4 file for the requested native-decision local obstruction checks.

The file uses the standard 2-isogeny quartic

```text
C(a,b,d): d * Y^2 = d^2 * X^4 + a*d*X^2*Z^2 + b*Z^4
```

for curves of the form

```text
y^2 = x^3 + a*x^2 + b*x.
```

For the N=16 curve it uses `a = -1, b = -1`; for the dual it uses
`a = 2, b = 5`.  The four certified finite searches are:

```text
E,      d =  5, modulo 125, primitive at 5
E,      d = -5, modulo 125, primitive at 5
E_dual, d = -1, modulo 16,  primitive at 2
E_dual, d = -5, modulo 16,  primitive at 2
```

One caution: the point list `O,(-1,0),(0,0),(1,0)` is not encoded in this file.
For the equation exactly as written, `y^2 = x^3 - x^2 - x`, substituting
`x = ±1` does not give `0` on the right-hand side.  The file below only
formalizes the requested local obstruction checks from the supplied descent
data.

```lean
/-
Copyright (c) 2026.

A small, self-contained native_decide file for the N = 16 obstruction curve

    E : y^2 = x^3 - x^2 - x

written in the 2-isogeny descent form

    C(a,b,d) : d * Y^2 = d^2 * X^4 + a*d*X^2*Z^2 + b*Z^4.

For E we use a = -1, b = -1.
For the dual 2-isogenous curve we use a = 2, b = 5.

The modular obstruction check below says that there is no residue solution
modulo n with (X,Z) primitive at the prime p dividing n.
-/

set_option maxHeartbeats 0

namespace DescentObstructionN16

/-- Square of a natural-number residue, computed as an integer. -/
def sqNat (x : Nat) : Int :=
  let xI : Int := Int.ofNat x
  xI * xI

/-- Fourth power of a natural-number residue, computed as an integer. -/
def fourthNat (x : Nat) : Int :=
  let x2 : Int := sqNat x
  x2 * x2

/--
The integer whose congruence to zero modulo `n` is the quartic equation

    d * Y^2 = d^2 * X^4 + a*d*X^2*Z^2 + b*Z^4.

The variables are represented by natural numbers in `List.range n`.
-/
def quarticExpr (a b d : Int) (x z y : Nat) : Int :=
  d * sqNat y -
    ((d * d) * fourthNat x
      + (a * d) * sqNat x * sqNat z
      + b * fourthNat z)

/-- Boolean congruence-to-zero test modulo `n`. -/
def congruentZeroMod (n : Nat) (v : Int) : Bool :=
  v % Int.ofNat n == 0

/-- The quartic equation, reduced modulo `n`. -/
def quarticHoldsMod (n : Nat) (a b d : Int) (x z y : Nat) : Bool :=
  congruentZeroMod n (quarticExpr a b d x z y)

/--
Primitive-at-`p` condition for a residue pair `(x,z)`, where `p ∣ n`.

Since the search only uses representatives in `List.range n`, this encodes

    not (p ∣ x and p ∣ z).
-/
def primitiveAt (p : Nat) (x z : Nat) : Bool :=
  !((x % p == 0) && (z % p == 0))

/--
Exhaustive finite check: there is no primitive residue solution to the quartic
modulo `n`, where primitivity is checked at `p`.
-/
def noPrimitiveQuarticSolutionsMod (n p : Nat) (a b d : Int) : Bool :=
  let residues := List.range n
  residues.all (fun x =>
    residues.all (fun z =>
      (!(primitiveAt p x z)) ||
        residues.all (fun y =>
          !(quarticHoldsMod n a b d x z y))))

/-- Proposition wrapper for the Boolean obstruction check. -/
def NoPrimitiveSolutionMod (n p : Nat) (a b d : Int) : Prop :=
  noPrimitiveQuarticSolutionsMod n p a b d = true

/-- N = 16 obstruction curve `E : y^2 = x^3 - x^2 - x`. -/
abbrev E_a : Int := -1
abbrev E_b : Int := -1

/-- Dual 2-isogenous curve, with `a' = -2a = 2`, `b' = a^2 - 4b = 5`. -/
abbrev Edual_a : Int := 2
abbrev Edual_b : Int := 5

/-
For E and d = 5, the checked equation modulo 125 is

    5*Y^2 = 25*X^4 - 5*X^2*Z^2 - Z^4.
-/
theorem E_d5_mod125_obstruction :
    NoPrimitiveSolutionMod 125 5 E_a E_b 5 := by
  native_decide

/-
For E and d = -5, the checked equation modulo 125 is

    -5*Y^2 = 25*X^4 + 5*X^2*Z^2 - Z^4.
-/
theorem E_dneg5_mod125_obstruction :
    NoPrimitiveSolutionMod 125 5 E_a E_b (-5) := by
  native_decide

/-
For the dual curve and d = -1, the checked equation modulo 16 is

    -Y^2 = X^4 - 2*X^2*Z^2 + 5*Z^4.
-/
theorem Edual_dneg1_mod16_obstruction :
    NoPrimitiveSolutionMod 16 2 Edual_a Edual_b (-1) := by
  native_decide

/-
For the dual curve and d = -5, the checked equation modulo 16 is

    -5*Y^2 = 25*X^4 - 10*X^2*Z^2 + 5*Z^4.
-/
theorem Edual_dneg5_mod16_obstruction :
    NoPrimitiveSolutionMod 16 2 Edual_a Edual_b (-5) := by
  native_decide

end DescentObstructionN16
```
