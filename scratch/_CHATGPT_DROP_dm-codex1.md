# Q2496 Euler auxiliary factor refinement

## Verdict

The arithmetic refinement is **true mathematically**: two positive coprime factorizations

```text
A = U*V = U'*V',   IsCoprime U V,   IsCoprime U' V'
```

refine into the four intersection factors

```text
alpha = part common to U and U'
b     = part common to U and V'
c     = part common to V and U'
d     = part common to V and V'
```

with

```text
U  = alpha*b,   V  = c*d,
U' = alpha*c,   V' = b*d,
A  = alpha*b*c*d.
```

Under the parity hypotheses of the requested theorem, `alpha` is even, so writing `alpha = 2*a` gives exactly

```text
U  = 2*a*b,   V  = c*d,
U' = 2*a*c,   V' = b*d,
A  = 2*a*b*c*d.
```

So there is no mathematical counterexample to the intended theorem.

The Lean issue is different: the requested declaration

```lean
theorem two_coprime_factorizations_refine_even_pos ... :
    RefinedFactors A U V U' V'
```

is the wrong interface for a data-valued result.  `RefinedFactors ...` is a `Type`, not a `Prop`.  Use one of these instead:

1. a Prop-valued theorem

```lean
theorem two_coprime_factorizations_refine_even_pos_nonempty ... :
    Nonempty (RefinedFactors A U V U' V')
```

2. or, after proving that theorem, a data-valued wrapper

```lean
noncomputable def two_coprime_factorizations_refine_even_pos_data ... :
    RefinedFactors A U V U' V' :=
  Classical.choice (two_coprime_factorizations_refine_even_pos_nonempty ...)
```

This also avoids the `propRecLargeElim` failure: it is legal to eliminate Prop-valued existentials while proving a Prop such as `Nonempty ...`; it is not legal to `rcases` a Prop existential directly while constructing arbitrary Type-level data unless you go through `Classical.choice` or define the witnesses explicitly.

The full simultaneous gcd-intersection refinement is a real lemma, not a one-line Mathlib call.  I would not try to prove the adjusted final theorem in one shot.  First prove a raw positive coprime factorization refinement with shared factor `alpha`; then use the compile-ready helper below to halve an even `alpha` and produce the requested `RefinedFactors`.

---

## Corrected theorem targets

Use these as the statement-layer targets.

```lean
/-- Raw refinement of two positive coprime factorizations.  No parity yet. -/
def two_coprime_factorizations_refine_raw_pos_statement : Prop :=
  ∀ {A U V U' V' : ℤ},
    A = U * V →
    A = U' * V' →
    0 < U → 0 < V → 0 < U' → 0 < V' →
    IsCoprime U V →
    IsCoprime U' V' →
    Nonempty (RawRefinedFactors A U V U' V')

/-- Final parity-refined statement.  This is the Prop-valued version of the requested target. -/
def two_coprime_factorizations_refine_even_pos_statement : Prop :=
  ∀ {A U V U' V' : ℤ},
    0 < A →
    A = U * V →
    A = U' * V' →
    0 < U → 0 < V → 0 < U' → 0 < V' →
    Even U → Even U' →
    Odd V → Odd V' →
    IsCoprime U V →
    IsCoprime U' V' →
    Nonempty (RefinedFactors A U V U' V')
```

The intended proof route is:

1. Prove `two_coprime_factorizations_refine_raw_pos_statement`, defining the raw factors by gcd intersections, for example
   ```text
   alpha = gcd U U'
   b     = gcd U V'
   c     = gcd V U'
   d     = gcd V V'
   ```
   with casts/absolute values handled carefully.
2. Prove `Even alpha` from `Even U`, `U = alpha*b`, `Odd V'`, and `V' = b*d`.
3. Apply `RawRefinedFactors.toRefined_nonempty` below.

---

## Compile-ready helper code

This code is designed to compile as a small local file.  It fixes the Type/Prop split and gives the first reusable helper layer: positive coprime factorizations plus conversion from a raw four-factor refinement with even shared factor to the requested `RefinedFactors`.

```lean
import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic

structure PairwiseCoprime2abcd (a b c d : ℤ) : Prop where
  hab : IsCoprime a b
  hac : IsCoprime a c
  had : IsCoprime a d
  hbc : IsCoprime b c
  hbd : IsCoprime b d
  hcd : IsCoprime c d

structure RefinedFactors (A U V U' V' : ℤ) where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  ha_pos : 0 < a
  hb_pos : 0 < b
  hc_pos : 0 < c
  hd_pos : 0 < d
  hU : U = 2 * a * b
  hV : V = c * d
  hU' : U' = 2 * a * c
  hV' : V' = b * d
  hA : A = 2 * a * b * c * d
  hpair : PairwiseCoprime2abcd a b c d

/-- A Type-valued package for one positive coprime factorization `A = left*right`. -/
structure PosCoprimeFactorization (A : ℤ) where
  left : ℤ
  right : ℤ
  hleft_pos : 0 < left
  hright_pos : 0 < right
  hmul : A = left * right
  hcop : IsCoprime left right

namespace PosCoprimeFactorization

/-- Pack explicit positive coprime factors as data. -/
def ofFactors {A L R : ℤ}
    (hmul : A = L * R)
    (hLpos : 0 < L)
    (hRpos : 0 < R)
    (hcop : IsCoprime L R) :
    PosCoprimeFactorization A where
  left := L
  right := R
  hleft_pos := hLpos
  hright_pos := hRpos
  hmul := hmul
  hcop := hcop

@[simp] theorem ofFactors_left {A L R : ℤ}
    (hmul : A = L * R)
    (hLpos : 0 < L)
    (hRpos : 0 < R)
    (hcop : IsCoprime L R) :
    (ofFactors hmul hLpos hRpos hcop).left = L := rfl

@[simp] theorem ofFactors_right {A L R : ℤ}
    (hmul : A = L * R)
    (hLpos : 0 < L)
    (hRpos : 0 < R)
    (hcop : IsCoprime L R) :
    (ofFactors hmul hLpos hRpos hcop).right = R := rfl

/-- Positivity of the product follows from positivity of both factors. -/
theorem A_pos {A : ℤ} (F : PosCoprimeFactorization A) : 0 < A := by
  rw [F.hmul]
  exact mul_pos F.hleft_pos F.hright_pos

/-- Swap the two factors. -/
def swap {A : ℤ} (F : PosCoprimeFactorization A) : PosCoprimeFactorization A where
  left := F.right
  right := F.left
  hleft_pos := F.hright_pos
  hright_pos := F.hleft_pos
  hmul := by
    rw [F.hmul, mul_comm]
  hcop := F.hcop.symm

/-- Pack the two input factorizations of the Euler auxiliary step. -/
def twoFromInputs {A U V U' V' : ℤ}
    (hUV : A = U * V)
    (hU'V' : A = U' * V')
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hU'pos : 0 < U') (hV'pos : 0 < V')
    (hUVcop : IsCoprime U V)
    (hU'V'cop : IsCoprime U' V') :
    PosCoprimeFactorization A × PosCoprimeFactorization A :=
  ⟨ofFactors hUV hUpos hVpos hUVcop,
   ofFactors hU'V' hU'pos hV'pos hU'V'cop⟩

end PosCoprimeFactorization

/-- Raw four-intersection refinement of two coprime factorizations.

Think of `alpha` as the shared `U`/`U'` part.  The final requested factor `a`
will be `alpha/2` after parity proves `Even alpha`.
-/
structure RawRefinedFactors (A U V U' V' : ℤ) where
  alpha : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  halpha_pos : 0 < alpha
  hb_pos : 0 < b
  hc_pos : 0 < c
  hd_pos : 0 < d
  hU : U = alpha * b
  hV : V = c * d
  hU' : U' = alpha * c
  hV' : V' = b * d
  hA : A = alpha * b * c * d
  hpair : PairwiseCoprime2abcd alpha b c d

namespace RawRefinedFactors

/-- If the shared raw factor `alpha` is even, halve it and obtain the requested
`RefinedFactors` package.

The conclusion is `Nonempty ...` on purpose: this permits eliminating the
`Even alpha` witness, which is a Prop-valued existential, without hitting
`propRecLargeElim`.
-/
theorem toRefined_nonempty {A U V U' V' : ℤ}
    (R : RawRefinedFactors A U V U' V')
    (halpha_even : Even R.alpha) :
    Nonempty (RefinedFactors A U V U' V') := by
  rcases halpha_even with ⟨a, ha⟩
  have ha_pos : 0 < a := by
    nlinarith [R.halpha_pos, ha]
  have ha_dvd_alpha : a ∣ R.alpha := by
    refine ⟨2, ?_⟩
    rw [ha]
    ring
  refine ⟨{
    a := a
    b := R.b
    c := R.c
    d := R.d
    ha_pos := ha_pos
    hb_pos := R.hb_pos
    hc_pos := R.hc_pos
    hd_pos := R.hd_pos
    hU := ?_
    hV := R.hV
    hU' := ?_
    hV' := R.hV'
    hA := ?_
    hpair := ?_
  }⟩
  · rw [R.hU, ha]
    ring
  · rw [R.hU', ha]
    ring
  · rw [R.hA, ha]
    ring
  · exact {
      hab := R.hpair.hab.of_isCoprime_of_dvd_left ha_dvd_alpha
      hac := R.hpair.hac.of_isCoprime_of_dvd_left ha_dvd_alpha
      had := R.hpair.had.of_isCoprime_of_dvd_left ha_dvd_alpha
      hbc := R.hpair.hbc
      hbd := R.hpair.hbd
      hcd := R.hpair.hcd
    }

/-- Data-valued wrapper, if a downstream construction really wants data rather
than a Prop-level `Nonempty`. -/
noncomputable def toRefined {A U V U' V' : ℤ}
    (R : RawRefinedFactors A U V U' V')
    (halpha_even : Even R.alpha) :
    RefinedFactors A U V U' V' :=
  Classical.choice (RawRefinedFactors.toRefined_nonempty R halpha_even)

end RawRefinedFactors
```

---

## Next proof obligation: raw gcd-intersection refinement

The next honest lemma to prove is the raw refinement theorem:

```lean
-- statement shape only; prove after the helper above is in place
theorem two_coprime_factorizations_refine_raw_pos
    {A U V U' V' : ℤ}
    (hUV : A = U * V)
    (hU'V' : A = U' * V')
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hU'pos : 0 < U') (hV'pos : 0 < V')
    (hUVcop : IsCoprime U V)
    (hU'V'cop : IsCoprime U' V') :
    Nonempty (RawRefinedFactors A U V U' V') := by
  -- define alpha,b,c,d from gcd intersections and prove the identities
  -- alpha = gcd U U'
  -- b     = gcd U V'
  -- c     = gcd V U'
  -- d     = gcd V V'
  -- This is the genuine gcd bookkeeping lemma; do not try to fold it into
  -- the final parity theorem.
  ...
```

For this lemma, the useful APIs are:

```lean
Int.isCoprime_iff_nat_coprime
Int.gcd_def
Int.natAbs_mul
Int.natCast_dvd
Nat.gcd_dvd_left
Nat.gcd_dvd_right
Nat.dvd_gcd
IsCoprime.mul_left
IsCoprime.mul_right
IsCoprime.of_mul_left_left
IsCoprime.of_mul_left_right
IsCoprime.of_mul_right_left
IsCoprime.of_mul_right_right
IsCoprime.of_isCoprime_of_dvd_left
IsCoprime.of_isCoprime_of_dvd_right
```

Proof plan for the raw lemma:

1. Work primarily with natural absolute values, because all factors are positive.
2. Define the four intersections by gcds.
3. Use `IsCoprime U V` to show a prime-power cannot appear in both `U` and `V`; use `IsCoprime U' V'` similarly for the second factorization.
4. Prove the row/column identities `U = alpha*b`, `V = c*d`, `U' = alpha*c`, `V' = b*d`.
5. Prove pairwise coprimality of `alpha,b,c,d` from the row/column coprimality constraints.
6. Then parity is separate: from `U = alpha*b`, `Even U`, and oddness of `b` obtained from `V' = b*d` and `Odd V'`, prove `Even alpha` and call `RawRefinedFactors.toRefined_nonempty`.

Bottom line: the exact arithmetic theorem is true, but the compile-feasible Lean interface should be `Nonempty (RefinedFactors ...)` plus a raw four-intersection refinement helper.  The code above is the compile-ready first layer and directly fixes the earlier `Prop`/`Type` and `propRecLargeElim` failures.
