# Q2656 (dm-codex1): Lean-feasible route for `IntQuarticEisensteinPrimitive`

Repo path mentioned by requester: `/Users/huangx/repos/flt-ai`  
GitHub repo/branch: `xiangyazi24/FLT`, branch `scratch`

Pinned Mathlib revision from `lake-manifest.json` on `scratch`:

```text
96fd0fff3b8837985ae21dd02e712cb5df72ec05
```

Target:

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples

-- project-local target shape:
def IntQuarticEisensteinPrimitive : Prop :=
  ∀ {A N S : ℤ}, IsCoprime A N → N ≠ 0 →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 → A = 0 ∨ A ^ 2 = N ^ 2
```

## Verdict

Use the cyclotomic/PID route over `𝓞 (CyclotomicField 3 ℚ)`.  Pinned Mathlib has the crucial infrastructure:

* ring of integers of the third cyclotomic field;
* PID instance for that ring;
* explicit unit list `{±1, ±η, ±η^2}`;
* `η^2 = -η - 1`;
* Kummer-style congruence lemma for units;
* generic PID/UFD square extraction from coprime factors.

There is no obvious dedicated `EisensteinInt`/pair type in pinned Mathlib.  The shortest Lean path is therefore to work directly in `𝓞 K`, with `K = CyclotomicField 3 ℚ`, and add a thin coefficient layer for elements `a + bη`.

The critical missing work is not PID square extraction.  It is the final **unit coefficient case analysis** after proving `A^2 + N^2η` is associated to a square.

## 1. Exact Mathlib API / grep targets

### Main cyclotomic files

```bash
grep -R "namespace IsCyclotomicExtension.Rat.Three" \
  .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean

grep -R "theorem three_pid" \
  .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean

grep -R "integralPowerBasisOfPrimePow\|toInteger" \
  .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean

grep -R "galEquivZMod" \
  .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean

grep -R "def norm\|coe_norm_int\|norm_algebraMap" \
  .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Norm.lean
```

### Names/signatures to use

From `Mathlib.NumberTheory.NumberField.Cyclotomic.Three`:

```lean
namespace IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (u : (𝓞 K)ˣ)

local notation3 "η" =>
  (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

lemma coe_eta : (η : 𝓞 K) = hζ.toInteger := rfl

lemma eta_sq : (η ^ 2 : 𝓞 K) = -η - 1

lemma eta_sq_add_eta_add_one : (η : 𝓞 K) ^ 2 + η + 1 = 0

theorem Units.mem [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
  u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2]

theorem eq_one_or_neg_one_of_unit_of_congruent
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (hcong : ∃ n : ℤ, λ ^ 2 ∣ (u - n : 𝓞 K)) :
    u = 1 ∨ u = -1

lemma lambda_dvd_or_dvd_sub_one_or_dvd_add_one
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] (x : 𝓞 K) :
    λ ∣ x ∨ λ ∣ x - 1 ∨ λ ∣ x + 1

lemma cube_sub_one_eq_mul (x : 𝓞 K) :
    x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)

lemma lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {x : 𝓞 K} (h : ¬ λ ∣ x) :
    λ ^ 4 ∣ x ^ 3 - 1 ∨ λ ^ 4 ∣ x ^ 3 + 1

end IsCyclotomicExtension.Rat.Three
```

From `Mathlib.NumberTheory.NumberField.Cyclotomic.PID`:

```lean
namespace IsCyclotomicExtension.Rat

variable (K : Type*) [Field K] [NumberField K]

theorem three_pid [IsCyclotomicExtension {3} ℚ K] :
  IsPrincipalIdealRing (𝓞 K)

end IsCyclotomicExtension.Rat
```

From `Mathlib.NumberTheory.NumberField.Cyclotomic.Basic`:

```lean
namespace IsCyclotomicExtension.Rat

theorem finrank [NeZero k] [IsCyclotomicExtension {k} ℚ K] :
  Module.finrank ℚ K = k.totient

theorem isIntegralClosure_adjoin_singleton_of_prime
    [IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) :
  IsIntegralClosure (Algebra.adjoin ℤ ({ζ} : Set K)) ℤ K

end IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

abbrev toInteger {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : 𝓞 K :=
  ⟨ζ, hζ.isIntegral (NeZero.pos _)⟩

noncomputable def integralPowerBasisOfPrimePow
    [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
  PowerBasis ℤ (𝓞 K)

end IsPrimitiveRoot
```

From `Mathlib.NumberTheory.NumberField.Norm`:

```lean
theorem Algebra.coe_norm_int {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
  (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K)

namespace RingOfIntegers

noncomputable def norm : 𝓞 L →* 𝓞 K

@[simp] lemma coe_norm (x : 𝓞 L) :
  norm K x = Algebra.norm K (x : L)

theorem norm_algebraMap (x : 𝓞 K) :
  norm K (algebraMap (𝓞 K) (𝓞 L) x) = x ^ finrank K L

end RingOfIntegers
```

From `Mathlib.RingTheory.PrincipalIdealDomain`:

```lean
namespace PrincipalIdealRing

instance (priority := 100) to_uniqueFactorizationMonoid
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
  UniqueFactorizationMonoid R

end PrincipalIdealRing

theorem exists_associated_pow_of_mul_eq_pow'
    [CommRing R] [IsDomain R] [IsBezout R]
    {a b c : R} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ k) :
  ∃ d : R, Associated (d ^ k) a

theorem exists_associated_pow_of_associated_pow_mul
    [CommRing R] [IsDomain R] [IsBezout R]
    {a b c : R} (hab : IsCoprime a b) {k : ℕ}
    (h : Associated (c ^ k) (a * b)) :
  ∃ d : R, Associated (d ^ k) a
```

Useful elementary files:

```bash
grep -R "theorem not_fermat_42\|def Fermat42" \
  .lake/packages/mathlib/Mathlib/NumberTheory/FLT/Four.lean

grep -R "sq_of_gcd_eq_one\|sq_of_isCoprime" \
  .lake/packages/mathlib/Mathlib/RingTheory/Int/Basic.lean

grep -R "coprime_classification'\|def PythagoreanTriple" \
  .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
```

## 2. Norm expression

Classically, this is the homogeneous square-value equation for the cyclotomic polynomial `Φ₁₂`:

```text
A^4 - A^2*N^2 + N^4 = Norm_{ℚ(ζ₃)/ℚ}(A^2 + N^2*η),
where η^2 + η + 1 = 0.
```

Do not start with the abstract `RingOfIntegers.norm` unless needed.  The product identity is shorter and avoids coercion noise:

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.PrincipalIdealDomain

open NumberField
open IsCyclotomicExtension.Rat.Three

noncomputable section

namespace EisensteinQuarticPlan

local notation "K₃" => CyclotomicField 3 ℚ

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

local notation3 "η" =>
  (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

-- Pseudo-code / target statement: fill proof by `rw [eta_sq]` and `ring`.
-- def alpha (A N : ℤ) : 𝓞 K :=
--   ((A ^ 2 : ℤ) : 𝓞 K) + ((N ^ 2 : ℤ) : 𝓞 K) * (η : 𝓞 K)
--
-- def alphaConj (A N : ℤ) : 𝓞 K :=
--   ((A ^ 2 : ℤ) : 𝓞 K) + ((N ^ 2 : ℤ) : 𝓞 K) * ((η : 𝓞 K) ^ 2)
--
-- theorem alpha_mul_alphaConj (A N : ℤ) :
--   alpha hζ A N * alphaConj hζ A N =
--     ((A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 : ℤ) : 𝓞 K)
--
-- theorem alpha_mul_alphaConj_eq_square
--     {A N S : ℤ}
--     (h : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
--   alpha hζ A N * alphaConj hζ A N = (((S : ℤ) : 𝓞 K) ^ 2)

end EisensteinQuarticPlan
```

If using `RingOfIntegers.norm`, first prove the same identity and then identify `alphaConj` with the nontrivial Galois conjugate.  `galEquivZMod` and `galEquivZMod_smul_of_pow_eq` in `Cyclotomic/Galois.lean` are the likely route, but the direct product identity is simpler.

## 3. Proof DAG

### Layer A: coefficient model `a + bη`

Add a local coefficient API instead of introducing a new ring type.

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

open NumberField
open IsCyclotomicExtension.Rat.Three

noncomputable section

namespace EisensteinQuarticPlan

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

local notation3 "η" =>
  (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit

-- theorem shape: every algebraic integer is uniquely `a + bη`.
-- Prove using `hζ.integralPowerBasisOfPrimePow` with `3 = 3^1`, or via
-- `isIntegralClosure_adjoin_singleton_of_prime` plus `finrank = 2`.
--
-- theorem exists_eta_coords (x : 𝓞 K) :
--   ∃ a b : ℤ, x = ((a : ℤ) : 𝓞 K) + ((b : ℤ) : 𝓞 K) * (η : 𝓞 K)
--
-- theorem eta_coords_ext {a b c d : ℤ}
--     (h : ((a : ℤ) : 𝓞 K) + ((b : ℤ) : 𝓞 K) * (η : 𝓞 K)
--        = ((c : ℤ) : 𝓞 K) + ((d : ℤ) : 𝓞 K) * (η : 𝓞 K)) :
--   a = c ∧ b = d

end EisensteinQuarticPlan
```

This coefficient layer is mandatory for the final unit cases.  It is also useful for the coprimality proof.

### Layer B: exclude the ramified prime `λ`

Key quotient fact: modulo `λ`, `η ≡ 1`, so

```text
A^2 + N^2η ≡ A^2 + N^2 mod λ.
```

Primitive `(A,N)` implies `3 ∤ A^2 + N^2`: if one of `A,N` is divisible by `3`, the other contributes `1`; if neither is divisible by `3`, both squares are `1`, so the sum is `2` modulo `3`.

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.Data.ZMod.Basic

-- theorem shape:
-- theorem three_not_dvd_sq_add_sq_of_isCoprime
--     {A N : ℤ} (hcop : IsCoprime A N) :
--   ¬ (3 : ℤ) ∣ A ^ 2 + N ^ 2
--
-- theorem lambda_not_dvd_alpha_of_isCoprime
--     {A N : ℤ} (hcop : IsCoprime A N) :
--   ¬ (hζ.toInteger - 1) ∣ alpha hζ A N
```

Implementation notes:

* Grep `toInteger_sub_one_dvd_prime'`, `norm_toInteger_sub_one_of_prime_ne_two'`, and `card_quotient_toInteger_sub_one` in cyclotomic files.
* If quotient transport is painful, prove directly: from `λ ∣ alpha`, use `λ ∣ η - 1`, rewrite `alpha - (A^2+N^2)` as a multiple of `λ`, hence `λ ∣ ((A^2+N^2 : ℤ) : 𝓞 K)`.  Then use the norm/divisibility lemma already used in FLT3: `Ideal.norm_dvd_iff` together with `hζ.norm_toInteger_sub_one_of_prime_ne_two'`.

### Layer C: coprime factors

Target:

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.RingTheory.PrincipalIdealDomain

-- theorem shape:
-- theorem alpha_coprime_alphaConj_of_isCoprime
--     {A N : ℤ} (hcop : IsCoprime A N) :
--   IsCoprime (alpha hζ A N) (alphaConj hζ A N)
```

Adversarial check: this is the first nontrivial algebraic-number-theory lemma, but it should not be the worst one.

Proof outline:

1. Use `isCoprime_of_irreducible_dvd` or `isCoprime_of_prime_dvd` from `PrincipalIdealDomain.lean`.
2. Let irreducible `p` divide both `alpha` and `alphaConj`.
3. Then `p` divides their difference:

   ```text
   alpha - alphaConj = N^2 * (η - η^2).
   ```

4. Also take a linear combination to get divisibility of something proportional to `A^2 * (η - η^2)`.
5. Because `IsCoprime A N`, any common divisor must lie over the ramified prime above `3`, i.e. be associated to `λ`.
6. But `lambda_not_dvd_alpha_of_isCoprime` excludes `λ ∣ alpha`.

Useful local lemmas to add:

```lean
-- theorem shape:
-- theorem eta_sub_eta_sq_associated_lambda_unit :
--   Associated ((η : 𝓞 K) - (η : 𝓞 K) ^ 2) (hζ.toInteger - 1)
--
-- theorem irreducible_dvd_intCast_sq_of_dvd_alpha_and_alphaConj
--     {p : 𝓞 K} (hp : Irreducible p)
--     (hpα : p ∣ alpha hζ A N) (hpαc : p ∣ alphaConj hζ A N) :
--   p ∣ ((A ^ 2 : ℤ) : 𝓞 K) ∧ p ∣ ((N ^ 2 : ℤ) : 𝓞 K) ∨
--   p ∣ (hζ.toInteger - 1)
```

### Layer D: square extraction in the PID

This part is already essentially in Mathlib.

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.RingTheory.PrincipalIdealDomain

-- theorem shape:
-- theorem alpha_associated_square_of_solution
--     {A N S : ℤ}
--     (hcop : IsCoprime A N)
--     (hEq : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
--   ∃ β : 𝓞 K, Associated (β ^ 2) (alpha hζ A N) := by
--   classical
--   haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
--   -- `IsPrincipalIdealRing` gives `IsBezout` and UFD instances.
--   -- apply `exists_associated_pow_of_mul_eq_pow'`
--   --   (alpha_coprime_alphaConj_of_isCoprime hζ hcop)
--   --   (alpha_mul_alphaConj_eq_square hζ hEq)
```

Then convert associatedness into a unit equation:

```lean
-- theorem shape:
-- theorem alpha_eq_unit_mul_square_of_solution
--     {A N S : ℤ}
--     (hcop : IsCoprime A N)
--     (hEq : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
--   ∃ (u : (𝓞 K)ˣ) (β : 𝓞 K),
--     alpha hζ A N = (u : 𝓞 K) * β ^ 2
```

### Layer E: enumerate units and compare coefficients

This is the hard missing lemma.

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

-- theorem shape:
-- theorem unit_square_coeffs_force_degenerate
--     {A N x y : ℤ} {u : (𝓞 K)ˣ}
--     (hcop : IsCoprime A N)
--     (hu : u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2])
--     (h : alpha hζ A N =
--       (u : 𝓞 K) *
--       (((x : ℤ) : 𝓞 K) + ((y : ℤ) : 𝓞 K) * (η : 𝓞 K)) ^ 2) :
--   A = 0 ∨ A ^ 2 = N ^ 2
```

Coefficient formulas to prove once by `rw [eta_sq]`; `ring`:

```text
(x + yη)^2       = (x^2 - y^2)      + (2xy - y^2)η
η*(x + yη)^2     = (y^2 - 2xy)      + (x^2 - 2xy)η
η^2*(x + yη)^2   = (2xy - x^2)      + (y^2 - x^2)η
```

The negative-unit cases negate both coefficients.  Since

```text
alpha(A,N) = A^2 + N^2η,
```

each unit case gives two integer equations.  The final integer lemma should be isolated, with no cyclotomic imports:

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic

-- theorem shape; one version per unit case is easiest to debug.
-- theorem coeff_case_one
--     {A N x y : ℤ} (hcop : IsCoprime A N)
--     (hA : A ^ 2 = x ^ 2 - y ^ 2)
--     (hN : N ^ 2 = 2 * x * y - y ^ 2) :
--   A = 0 ∨ A ^ 2 = N ^ 2
--
-- theorem coeff_case_eta
--     {A N x y : ℤ} (hcop : IsCoprime A N)
--     (hA : A ^ 2 = y ^ 2 - 2 * x * y)
--     (hN : N ^ 2 = x ^ 2 - 2 * x * y) :
--   A = 0 ∨ A ^ 2 = N ^ 2
--
-- theorem coeff_case_eta_sq
--     {A N x y : ℤ} (hcop : IsCoprime A N)
--     (hA : A ^ 2 = 2 * x * y - x ^ 2)
--     (hN : N ^ 2 = y ^ 2 - x ^ 2) :
--   A = 0 ∨ A ^ 2 = N ^ 2
```

Recommended proof style for those integer cases:

* use parity/mod-3/mod-4 first to kill negative-unit cases where both coefficients are nonpositive or impossible for squares;
* use `Int.sq_of_isCoprime` / `Int.sq_of_gcd_eq_one` when a product of coprime integers is a square;
* use `PythagoreanTriple.coprime_classification'` when an equation becomes a primitive Pythagorean triple.

This coefficient block is where most Lean time will be spent.  Keep it isolated from cyclotomic imports so `ring`, `omega`, `nlinarith`, and `ZMod` debugging stays fast.

### Final assembly

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.RingTheory.PrincipalIdealDomain

-- theorem shape:
-- theorem intQuarticEisensteinPrimitive_cyclotomic :
--   IntQuarticEisensteinPrimitive := by
--   intro A N S hcop hN hEq
--   classical
--   let K := CyclotomicField 3 ℚ
--   let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
--   haveI : NumberField K := IsCyclotomicExtension.numberField {3} ℚ K
--   haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
--   obtain ⟨u, β, hβ⟩ := alpha_eq_unit_mul_square_of_solution hζ hcop hEq
--   obtain ⟨x, y, hxy⟩ := exists_eta_coords hζ β
--   rw [hxy] at hβ
--   exact unit_square_coeffs_force_degenerate hζ hcop (Units.mem hζ u) hβ
```

## 4. Can this be derived from `not_fermat_42`?

No direct derivation.

Mathlib FLT4 gives:

```lean
def Fermat42 (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2

theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ^ 4 + b ^ 4 ≠ c ^ 2
```

Our equation rewrites as:

```text
S^2 = A^4 - A^2*N^2 + N^4
    = (A^2 - N^2)^2 + (A*N)^2.
```

That is a Pythagorean triple with legs `A^2 - N^2` and `A*N`, not a Fermat42 equation with two fourth-power legs.  Applying `not_fermat_42` would require proving extra square/fourth-power structure for the legs; that is essentially the missing descent/classification work.  So `not_fermat_42` is useful as an API source, not as a theorem that closes this target.

Useful APIs from the FLT4 neighborhood:

```lean
-- from Mathlib.RingTheory.Int.Basic
theorem Int.sq_of_gcd_eq_one {a b c : ℤ}
    (h : Int.gcd a b = 1) (heq : a * b = c ^ 2) :
  ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2

theorem Int.sq_of_isCoprime {a b c : ℤ}
    (h : IsCoprime a b) (heq : a * b = c ^ 2) :
  ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2

-- from Mathlib.NumberTheory.PythagoreanTriples
def PythagoreanTriple (x y z : ℤ) : Prop :=
  x * x + y * y = z * z

theorem PythagoreanTriple.coprime_classification'
    {x y z : ℤ} (h : PythagoreanTriple x y z)
    (h_coprime : Int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) :
  ∃ m n,
    x = m ^ 2 - n ^ 2 ∧
      y = 2 * m * n ∧
        z = m ^ 2 + n ^ 2 ∧
          Int.gcd m n = 1 ∧
            (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m
```

## 5. Hardest missing lemma ranking

1. **Hardest: unit coefficient case.**  After `alpha = u * β^2`, enumerate six units and prove the resulting integer coefficient equations force `A=0 ∨ A^2=N^2`.  This is independent of E1/full-cover and should be implemented as pure integer lemmas.
2. **Medium: `alpha`/`alphaConj` coprime.**  Needs careful handling of the ramified prime `λ`.  The Mathlib cyclotomic file has enough local lemmas, but the proof will involve divisibility and associatedness.
3. **Easy: square extraction.**  `IsCyclotomicExtension.Rat.three_pid` plus `exists_associated_pow_of_mul_eq_pow'` is exactly the required PID/UFD tool.
4. **Easy: norm/product identity.**  One `rw [eta_sq]`; `ring` lemma.

## 6. Elementary fallback if cyclotomic API becomes too heavy

I do **not** recommend replacing the cyclotomic/PID plan with a raw elementary descent.  A safe fallback is only to use elementary number theory for the coefficient cases after the PID step.

If a fully elementary route is still desired, target a separate theorem around the conic identity:

```text
S^2 = A^4 - A^2*N^2 + N^4
⇔ S^2 + 3*(A*N)^2 = (A^2 + N^2)^2.
```

The first elementary theorem should be a parametrization of primitive solutions to `X^2 + 3Y^2 = Z^2`, not a vague descent:

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic

-- theorem shape:
-- theorem primitive_X_sq_add_three_Y_sq_param
--     {X Y Z : ℤ}
--     (hcop : IsCoprime X Y)
--     (hZ : 0 < Z)
--     (h : X ^ 2 + 3 * Y ^ 2 = Z ^ 2) :
--   ∃ r t : ℤ,
--     X = r ^ 2 - 3 * t ^ 2 ∧
--     Y = 2 * r * t ∧
--     Z = r ^ 2 + 3 * t ^ 2 ∧
--     IsCoprime r t
```

Then specialize:

```lean
-- theorem shape:
-- theorem eisenstein_quartic_conic_param
--     {A N S : ℤ}
--     (hcop : IsCoprime A N)
--     (hpos : 0 < A ^ 2 + N ^ 2)
--     (h : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
--   ∃ r t : ℤ,
--     S = r ^ 2 - 3 * t ^ 2 ∧
--     A * N = 2 * r * t ∧
--     A ^ 2 + N ^ 2 = r ^ 2 + 3 * t ^ 2 ∧
--     IsCoprime r t
```

This gives explicit parameters, but it does not yet give a verified smaller triple `(A',N',S')`.  I would reject any proposed elementary descent that does not provide checked formulas and a strictly decreasing measure.  In contrast, the cyclotomic plan reduces the problem to finite unit cases and pure integer lemmas without invoking E1/E24/full-cover residuals.

## Recommended implementation order

1. `EisensteinCoords.lean`: `exists_eta_coords`, `eta_coords_ext`, coordinate formulas for `β^2`, `η*β^2`, `η^2*β^2`.
2. `EisensteinNorm.lean`: `alpha`, `alphaConj`, `alpha_mul_alphaConj`.
3. `EisensteinCoprime.lean`: `lambda_not_dvd_alpha_of_isCoprime`, `alpha_coprime_alphaConj_of_isCoprime`.
4. `EisensteinSquare.lean`: `alpha_eq_unit_mul_square_of_solution` using `three_pid` and `exists_associated_pow_of_mul_eq_pow'`.
5. `EisensteinCoeffCases.lean`: pure integer coefficient cases.
6. `N12QuarticEisenstein.lean`: assemble `IntQuarticEisensteinPrimitive`.

This route is independent of the E1 finite-point theorem and of the full-cover residual theorem.  It uses only local cyclotomic arithmetic, PID/UFD extraction, and elementary integer lemmas.