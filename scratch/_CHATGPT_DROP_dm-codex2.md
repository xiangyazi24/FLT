# Q2768 dm-codex2: finite mod-`2^k` obstruction certificates for `CoverInt`

This is written as a Lean-oriented checklist plus code skeletons. I recommend using `ZMod m`, not `Fin m`, for the certificate search: the two cover equations are ring equations, integer coefficients including negative ones cast cleanly into `ZMod m`, and `native_decide` can enumerate `ZMod 4`, `ZMod 8`, `ZMod 16` directly.

The only subtle bridge is the primitive condition. For modulus `m = 4/8/16`, primitive over integers implies **not all four residues are even**, not “not all residues are nonzero modulo `m`”. In `ZMod m`, define “even residue” as membership in the image of multiplication by `2`.

## 0. Minimal imports and base definitions

If `CoverInt` and `PrimitiveInt4` are already defined in your file, keep those and import only the obstruction helpers.

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

/-- Integer cover equations.  Delete this if already defined. -/
def CoverInt (d0 d1 d3 A B C T : ℤ) : Prop :=
  d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2 ∧
  d3 * C ^ 2 - d0 * A ^ 2 = 3 * T ^ 2

/-- Integer projective primitivity.  Delete this if already defined. -/
def PrimitiveInt4 (A B C T : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ¬ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ B ∧ (p : ℤ) ∣ C ∧ (p : ℤ) ∣ T)

end MazurProof.RationalPointsN12
```

## 1. Finite cover predicate over `ZMod m`

Use a natural modulus. Add `[NeZero m]` so `ZMod m` is finite; for literals `4`, `8`, `16`, Lean usually infers this instance.

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

/-- The cover equations reduced modulo `m`. -/
def coverMod (m : ℕ) [NeZero m]
    (d0 d1 d3 : ℤ) (a b c t : ZMod m) : Prop :=
  (d0 : ZMod m) * a ^ 2 - (d1 : ZMod m) * b ^ 2 = t ^ 2 ∧
  (d3 : ZMod m) * c ^ 2 - (d0 : ZMod m) * a ^ 2 = (3 : ZMod m) * t ^ 2

/-- Optional `Fin m` wrapper.  Prefer `ZMod m` unless you have a reason not to. -/
def coverModFin (m : ℕ) [NeZero m]
    (d0 d1 d3 : ℤ) (a b c t : Fin m) : Prop :=
  coverMod m d0 d1 d3
    ((a.val : ℕ) : ZMod m)
    ((b.val : ℕ) : ZMod m)
    ((c.val : ℕ) : ZMod m)
    ((t.val : ℕ) : ZMod m)

end MazurProof.RationalPointsN12
```

Notes:

* Do not reduce `d0`, `d1`, `d3` by hand. Write `(d0 : ZMod m)` and let `norm_num`/kernel reduction handle it.
* Negative coefficients are fine: `(-1 : ℤ)` casts to the class `m-1` in `ZMod m`.
* Avoid `%` in the core definitions. `%` on negative integers quickly leads to `Int.emod`/`Nat.mod` coercion goals.

## 2. Primitive residue condition for moduli `2^k`

For `m = 4/8/16`, “even modulo `m`” means the residue is in the image of multiplication by `2`, i.e. `x = 2*y` for some `y : ZMod m`. Then primitive means **not all** four residues are even.

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

/-- `x` is an even residue modulo `m`: it lies in the image of multiplication by `2`. -/
def evenResidue (m : ℕ) [NeZero m] (x : ZMod m) : Prop :=
  ∃ y : ZMod m, x = (2 : ZMod m) * y

/-- Correct primitive residue test for moduli `2^k`: at least one coordinate is odd. -/
def primitiveMod2 (m : ℕ) [NeZero m] (a b c t : ZMod m) : Prop :=
  ¬ (evenResidue m a ∧ evenResidue m b ∧ evenResidue m c ∧ evenResidue m t)

/-- Local obstruction predicate: no primitive mod-`2` residue tuple solves the mod-`m` cover. -/
def localObstruction (m : ℕ) [NeZero m] (d0 d1 d3 : ℤ) : Prop :=
  ∀ a b c t : ZMod m,
    primitiveMod2 m a b c t →
      ¬ coverMod m d0 d1 d3 a b c t

/-- Equivalent existential form, sometimes convenient for debugging with `#eval decide`. -/
def badTupleExists (m : ℕ) [NeZero m] (d0 d1 d3 : ℤ) : Prop :=
  ∃ a b c t : ZMod m,
    primitiveMod2 m a b c t ∧ coverMod m d0 d1 d3 a b c t

end MazurProof.RationalPointsN12
```

For `m = 2`, `evenResidue 2 x` is just `x = 0`. For `m = 4/8/16`, it is `{0,2}`, `{0,2,4,6}`, `{0,2,4,6,8,10,12,14}` respectively. This is exactly what primitive integer tuples give after reduction: at least one of `A,B,C,T` is odd.

Do **not** use `a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ t ≠ 0` modulo `4/8/16`; an even but nonzero residue such as `2 : ZMod 8` still corresponds to an even integer coordinate.

## 3. Bridge: integer cover gives `coverMod`

This part is pure cast/ring API. The safest pattern is `congrArg (fun z : ℤ => (z : ZMod m))` followed by `simpa [coverMod]`.

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

theorem coverInt_to_coverMod
    {m : ℕ} [NeZero m]
    {d0 d1 d3 A B C T : ℤ}
    (h : CoverInt d0 d1 d3 A B C T) :
    coverMod m d0 d1 d3
      (A : ZMod m) (B : ZMod m) (C : ZMod m) (T : ZMod m) := by
  rcases h with ⟨h₁, h₂⟩
  constructor
  · have h₁' := congrArg (fun z : ℤ => (z : ZMod m)) h₁
    simpa [coverMod] using h₁'
  · have h₂' := congrArg (fun z : ℤ => (z : ZMod m)) h₂
    simpa [coverMod] using h₂'

end MazurProof.RationalPointsN12
```

If `simpa [coverMod]` leaves powers in a different shape, add `[pow_two]`:

```lean
simpa [coverMod, pow_two] using h₁'
```

Do not introduce `A % m` here. Casting to `ZMod m` is the intended API.

## 4. Bridge: primitive integers give `primitiveMod2`

Key generic lemma: if `m` is even and `(A : ZMod m)` is an even residue, then `A` is divisible by `2` in `ℤ`.

The proof uses the standard `ZMod` API:

```lean
#check ZMod.natCast_zmod_val
#check ZMod.intCast_zmod_eq_zero_iff_dvd
```

Expected helper shape:

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

/-- If an integer reduces to an even residue modulo an even modulus, then the integer is even. -/
theorem dvd_two_of_evenResidue_intCast
    {m : ℕ} [NeZero m] (hm2 : 2 ∣ m) {A : ℤ}
    (hA : evenResidue m (A : ZMod m)) :
    (2 : ℤ) ∣ A := by
  rcases hA with ⟨y, hy⟩

  -- Replace the abstract residue `y` by its canonical integer representative.
  have hyval : ((y.val : ℤ) : ZMod m) = y := by
    -- Usually works in current mathlib:
    exact_mod_cast (ZMod.natCast_zmod_val y)

  -- `A` is congruent modulo `m` to the even integer `2*y.val`.
  have hzero : ((A - 2 * (y.val : ℤ) : ℤ) : ZMod m) = 0 := by
    calc
      ((A - 2 * (y.val : ℤ) : ℤ) : ZMod m)
          = (A : ZMod m) - (2 : ZMod m) * ((y.val : ℤ) : ZMod m) := by
              norm_num
      _ = (A : ZMod m) - (2 : ZMod m) * y := by rw [hyval]
      _ = 0 := by
              rw [hy]
              ring

  -- Turn zero in `ZMod m` into divisibility by `m`.
  have hm_dvd : (m : ℤ) ∣ A - 2 * (y.val : ℤ) := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (n := m) (a := A - 2 * (y.val : ℤ))).mp hzero

  -- Since `m` is even, the congruence to an even integer makes `A` even.
  rcases hm2 with ⟨q, hq⟩
  rcases hm_dvd with ⟨r, hr⟩
  refine ⟨(q : ℤ) * r + (y.val : ℤ), ?_⟩
  have hqz : (m : ℤ) = 2 * (q : ℤ) := by
    exact_mod_cast hq
  calc
    A = (A - 2 * (y.val : ℤ)) + 2 * (y.val : ℤ) := by ring
    _ = (m : ℤ) * r + 2 * (y.val : ℤ) := by rw [hr]
    _ = 2 * ((q : ℤ) * r + (y.val : ℤ)) := by
          rw [hqz]
          ring

/-- Integer primitivity implies the finite mod-`2` primitive condition. -/
theorem primitiveInt4_to_primitiveMod2
    {m : ℕ} [NeZero m] (hm2 : 2 ∣ m)
    {A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T) :
    primitiveMod2 m (A : ZMod m) (B : ZMod m) (C : ZMod m) (T : ZMod m) := by
  intro hall
  rcases hall with ⟨hA, hB, hC, hT⟩
  exact hprim 2 (by norm_num) ⟨
    dvd_two_of_evenResidue_intCast (m := m) hm2 hA,
    dvd_two_of_evenResidue_intCast (m := m) hm2 hB,
    dvd_two_of_evenResidue_intCast (m := m) hm2 hC,
    dvd_two_of_evenResidue_intCast (m := m) hm2 hT⟩

end MazurProof.RationalPointsN12
```

If the exact theorem name for the divisibility bridge differs in your pinned Mathlib, search for these names:

```lean
#check ZMod.intCast_zmod_eq_zero_iff_dvd
#check ZMod.intCast_eq_intCast_iff_dvd_sub
#check Int.ModEq
```

The fallback is to prove `A ≡ 2*y.val [ZMOD m]`, use the `Int.ModEq` divisibility characterization, and then combine it with `2 ∣ m`.

## 5. Integer solution gives a checked finite tuple

Useful combined bridge theorem:

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

theorem intCoverPrimitive_to_modTuple
    {m : ℕ} [NeZero m] (hm2 : 2 ∣ m)
    {d0 d1 d3 A B C T : ℤ}
    (hcover : CoverInt d0 d1 d3 A B C T)
    (hprim : PrimitiveInt4 A B C T) :
    coverMod m d0 d1 d3
      (A : ZMod m) (B : ZMod m) (C : ZMod m) (T : ZMod m) ∧
    primitiveMod2 m
      (A : ZMod m) (B : ZMod m) (C : ZMod m) (T : ZMod m) := by
  exact ⟨
    coverInt_to_coverMod (m := m) hcover,
    primitiveInt4_to_primitiveMod2 (m := m) hm2 hprim⟩

end MazurProof.RationalPointsN12
```

## 6. Main soundness theorem for a certificate

Once a fixed triple has a `native_decide` proof of `localObstruction m d0 d1 d3`, the following theorem turns it into a no-primitive-integer-solution statement.

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

theorem noPrimitiveIntCover_of_localObstruction
    {m : ℕ} [NeZero m] (hm2 : 2 ∣ m)
    {d0 d1 d3 : ℤ}
    (hcert : localObstruction m d0 d1 d3) :
    ¬ ∃ A B C T : ℤ,
      CoverInt d0 d1 d3 A B C T ∧ PrimitiveInt4 A B C T := by
  rintro ⟨A, B, C, T, hcover, hprim⟩
  exact hcert
    (A : ZMod m) (B : ZMod m) (C : ZMod m) (T : ZMod m)
    (primitiveInt4_to_primitiveMod2 (m := m) hm2 hprim)
    (coverInt_to_coverMod (m := m) hcover)

end MazurProof.RationalPointsN12
```

## 7. Fixed certificate shape with `native_decide`

For each fixed triple `(d0,d1,d3)` and modulus `m`, write one local certificate theorem, then apply the soundness theorem.

Template:

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

-- Replace these constants by the actual fixed triple.
-- The constants must be concrete numerals for `native_decide` to close the finite search.

/-- Example shape only: replace `D0`, `D1`, `D3` by concrete integer numerals. -/
-- theorem cert_mod16_D0_D1_D3 :
--     localObstruction 16 (D0 : ℤ) (D1 : ℤ) (D3 : ℤ) := by
--   native_decide

/-- Example shape only: derived integer no-solution theorem. -/
-- theorem no_primitive_cover_D0_D1_D3 :
--     ¬ ∃ A B C T : ℤ,
--       CoverInt (D0 : ℤ) (D1 : ℤ) (D3 : ℤ) A B C T ∧
--       PrimitiveInt4 A B C T :=
--   noPrimitiveIntCover_of_localObstruction
--     (m := 16) (hm2 := by norm_num) cert_mod16_D0_D1_D3

end MazurProof.RationalPointsN12
```

A real certificate looks like this, with actual numerals:

```lean
-- theorem cert_mod8_neg1_5_13 :
--     localObstruction 8 (-1 : ℤ) (5 : ℤ) (13 : ℤ) := by
--   native_decide
--
-- theorem no_primitive_cover_neg1_5_13 :
--     ¬ ∃ A B C T : ℤ,
--       CoverInt (-1 : ℤ) (5 : ℤ) (13 : ℤ) A B C T ∧
--       PrimitiveInt4 A B C T :=
--   noPrimitiveIntCover_of_localObstruction
--     (m := 8) (hm2 := by norm_num) cert_mod8_neg1_5_13
```

Do not leave `D0 D1 D3` as variables in the certificate theorem; then the proposition is not finite/computable in the intended way and is generally false.

## 8. Performance-friendly variants

The generic `evenResidue` predicate is clean and sound, but its decidability searches for a witness `y : ZMod m`. For `m ≤ 16`, this is usually fine. If many certificates become slow, use a fixed-modulus fast parity predicate and prove it equivalent to `evenResidue` by finite checking.

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12

/-- Fast fixed-modulus parity test using the canonical representative. -/
def evenResidueVal (m : ℕ) [NeZero m] (x : ZMod m) : Prop :=
  x.val % 2 = 0

-- These fixed equivalences are finite and can often be closed by native computation.
-- Use them to rewrite the certificate predicate if generic `evenResidue` is slow.
-- theorem evenResidue_iff_val_4 (x : ZMod 4) :
--     evenResidue 4 x ↔ evenResidueVal 4 x := by
--   native_decide
--
-- theorem evenResidue_iff_val_8 (x : ZMod 8) :
--     evenResidue 8 x ↔ evenResidueVal 8 x := by
--   native_decide
--
-- theorem evenResidue_iff_val_16 (x : ZMod 16) :
--     evenResidue 16 x ↔ evenResidueVal 16 x := by
--   native_decide

end MazurProof.RationalPointsN12
```

If you use `evenResidueVal` directly in the soundness theorem, still prove the integer bridge through `evenResidue`, or prove the analogous lemma from `x.val % 2 = 0` using `ZMod.intCast_zmod_eq_zero_iff_dvd`. The mathematical reason is the same: `A` differs from the canonical representative by a multiple of even `m`.

## 9. Pitfalls checklist

* **`ZMod 0` is not finite.** Keep `[NeZero m]`; for `4`, `8`, `16` it is inferred.
* **Do not use `%` for integer reduction.** Prefer `(A : ZMod m)`. Negative integers plus `%` create avoidable `Int.emod` obligations.
* **`m=4/8/16` is not prime.** The primitive residue condition is not “not all zero modulo `m`”; it is “not all even residues”.
* **Do not require every coordinate to be nonzero.** Primitive projective tuples may have some zero coordinates.
* **Do not require a coordinate to be a unit unless you prove the equivalence.** For `2^k`, “odd residue” is equivalent to unit, but `primitiveMod2` avoids this extra API.
* **Use concrete numeral coefficients in certificates.** `native_decide` is for fixed triples, not symbolic triples.
* **For cover equation casting, use `congrArg` into `ZMod m`.** This keeps all ring-normalization local and avoids manual congruence modulo `m`.
* **For the primitive bridge, use only the prime `2`.** `PrimitiveInt4` is stronger than needed; the local obstruction modulo `2^k` only consumes the `p=2` case.
