# Q1477 (dm4): proving `B` is odd in the quartic equation

## Executive answer

The call-site denominator route does **not** prove `B` odd.  From

```text
w² = u³ + u² - u,
(u³ + u² - u).den = u.den³,
```

you only get that `u.den³` is a square, hence that every prime exponent in `u.den` is even.  That says `u.den` is itself a square.  It does **not** say that its square root `B₀` is odd.  The `2`-adic exponent of `u.den` could be `2, 4, 6, ...`, giving an even square root.

So yes: `both_odd` must be proved inside the quartic descent, not at the call site.

The working approach is not a local congruence proof.  Direct mod arithmetic only rules out

```text
v₂(B) = 1   -- i.e. B ≡ 2 mod 4.
```

The remaining case

```text
4 ∣ B
```

is handled by a **2-adic infinite descent**.  In other words, the even-`B` case is not a contradiction modulo `16`; it is a descent-producing case.

## Core theorem to prove

Instead of trying to prove `Odd B` as a standalone modular lemma, prove this descent lemma:

```lean
/-- Even-denominator descent for the primitive quartic equation.

If `(r,B,s)` is a primitive positive solution of
`s^2 = r^4 + r^2 * B^2 - B^4` and `B` is even, then there is a new primitive
positive solution `(r',B',s')` with `B'` even and `B' < B`.
-/
lemma quartic_even_descent
    {r B s : ℕ}
    (hr : 0 < r) (hB : 0 < B)
    (hcop : Nat.Coprime r B)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hBeven : Even B) :
    ∃ r' B' s' : ℕ,
      0 < r' ∧ 0 < B' ∧ B' < B ∧ Even B' ∧
      Nat.Coprime r' B' ∧
      s' ^ 2 = r' ^ 4 + r' ^ 2 * B' ^ 2 - B' ^ 4 := by
  -- This is the real arithmetic descent lemma; see the proof outline below.
  sorry
```

Then `B` odd is a short well-founded-descent wrapper:

```lean
import Mathlib.Tactic

namespace FLT.C20

/-- Bundle the primitive quartic equation.  Use the actual project statement if it already exists. -/
def QuarticSol (r B s : ℕ) : Prop :=
  0 < r ∧ 0 < B ∧ Nat.Coprime r B ∧
    s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

/-- The only hard input needed for the parity theorem. -/
axiom quartic_even_descent
    {r B s : ℕ} :
    QuarticSol r B s → Even B →
    ∃ r' B' s' : ℕ,
      QuarticSol r' B' s' ∧ Even B' ∧ B' < B

/-- No primitive positive solution can have even `B`. -/
theorem quartic_B_odd
    {r B s : ℕ} (hsol : QuarticSol r B s) : Odd B := by
  classical
  by_contra hBodd
  have hBeven : Even B := by
    exact (not_odd_iff_even).mp hBodd

  let Bad (B : ℕ) : Prop :=
    ∃ r s : ℕ, QuarticSol r B s ∧ Even B

  have noBad : ∀ B : ℕ, Bad B → False := by
    intro B
    induction B using Nat.strong_induction_on with
    | h B ih =>
        rintro ⟨r, s, hsol, hBeven⟩
        obtain ⟨r', B', s', hsol', hBeven', hlt⟩ :=
          quartic_even_descent (r := r) (B := B) (s := s) hsol hBeven
        exact ih B' hlt ⟨r', s', hsol', hBeven'⟩

  exact noBad B ⟨r, s, hsol, hBeven⟩

end FLT.C20
```

In the real file, replace the `axiom quartic_even_descent` with the construction below.  The wrapper is the important structural point: **prove oddness by excluding an infinite chain of smaller even denominators**.

## Why congruences alone fail

Assume `B` is even and `gcd(r,B)=1`.  Then `r` is odd.

If `B = 2C` with `C` odd, then modulo `16`:

```text
r⁴ ≡ 1,
r² B² ≡ 4,
B⁴ ≡ 0,
```

so

```text
s² = r⁴ + r²B² - B⁴ ≡ 5 mod 16,
```

impossible.  Thus the congruence proof only gives:

```text
B even ⇒ 4 ∣ B.
```

When `4 ∣ B`, the same mod-`16` check gives `s² ≡ 1 mod 16`, which is perfectly possible.  This is exactly why Q1448 saw no contradiction.

## The even-`B` descent construction

Assume now that `B` is even.  The mod-`16` argument above improves this to `4 ∣ B`.  Write

```text
B = 2C
```

so `C` is still even.

Start from

```text
s² = r⁴ + r²B² - B⁴.
```

Then

```text
(2r² + B²)² - (2s)² = 5B⁴.
```

Since `4 ∣ B` and `r,s` are odd, both factors are divisible by `4`.  Define

```text
M = (2r² + B² - 2s) / 4,
N = (2r² + B² + 2s) / 4.
```

Then

```text
M * N = 5 * C⁴,
M < N,
gcd(M,N) = 1.
```

The gcd proof is the first nontrivial bookkeeping point.  The useful observations are:

```text
M + N = r² + B²/2,
N - M = s.
```

Any common odd prime divisor of `M,N` divides `s` and `r² + B²/2`.  Substituting
`B² ≡ -2r²` into the quartic equation modulo that prime gives `-5r⁴ ≡ 0`.  Hence the prime is either `5` or divides `r`.  The `q ∣ r` case contradicts `gcd(r,B)=1`; the `q = 5` case is ruled out because if `5 ∣ M,N`, then `25 ∣ MN = 5C⁴`, so `5 ∣ C`, hence `5 ∣ B`, and then `5 ∣ s,B` forces `5 ∣ r`, again contradicting primitivity.

Now split coprime factors of `5*C⁴`:

```text
(M,N) = (a⁴, 5b⁴)
```

or

```text
(M,N) = (5a⁴, b⁴),
```

with

```text
C = a*b,
gcd(a,b)=1.
```

This is the standard `factorization` lemma for coprime factors of a fourth power times `5`.

### Case 1: `M = a⁴`, `N = 5b⁴`

Using `M+N = r² + 2C²` and `C = ab`, we get

```text
r² + 2a²b² = a⁴ + 5b⁴,
```

hence

```text
r² = a⁴ - 2a²b² + 5b⁴
   = (a² - b²)² + (2b²)².
```

This is a primitive Pythagorean triple:

```text
(a² - b²)² + (2b²)² = r².
```

Parametrize it.  There exist coprime `m > n > 0` of opposite parity such that

```text
2b² = 2mn,
|a² - b²| = m² - n²,
r = m² + n².
```

So

```text
b² = m*n.
```

Since `gcd(m,n)=1` and `m*n` is a square, both `m` and `n` are squares:

```text
m = x²,
n = y²,
b = x*y.
```

Because the original `C = ab` is even and the parity of the primitive triple forces the even leg to come from `b`, one gets `b` even and exactly one of `x,y` even.

Now use the sign of `a²-b²`.

If `a² > b²`, then

```text
a² - b² = x⁴ - y⁴,
b² = x²y²,
```

so

```text
a² = x⁴ + x²y² - y⁴.
```

Thus `(x, y, a)` is a new solution of the same quartic equation.  The mod-`4` orientation of the Pythagorean triple gives `y` even, and clearly `y < B`.

If `b² > a²`, then

```text
b² - a² = x⁴ - y⁴,
b² = x²y²,
```

so

```text
a² = y⁴ + y²x² - x⁴.
```

Thus `(y, x, a)` is a new solution, and the mod-`4` orientation gives `x` even.  Again `x < B`.

So in either subcase, an even-`B` solution gives a smaller even-`B` solution.

### Case 2: `M = 5a⁴`, `N = b⁴`

This is symmetric.  From

```text
r² + 2a²b² = 5a⁴ + b⁴
```

we get

```text
r² = (b² - a²)² + (2a²)².
```

Parametrize this primitive Pythagorean triple.  Since

```text
a² = m*n
```

with `gcd(m,n)=1`, write

```text
m = x²,
n = y²,
a = x*y.
```

The same sign split produces a new quartic solution with smaller even denominator.

This proves `quartic_even_descent`.

## Lean organization I recommend

Do not try to make one enormous proof term.  Split it into these lemmas:

```lean
namespace FLT.C20

/-- `B ≡ 2 mod 4` is impossible. -/
lemma quartic_not_two_mod_four
    {r B s : ℕ} (hsol : QuarticSol r B s)
    (hBeven : Even B) : 4 ∣ B := by
  -- prove by casting the equation to `ZMod 16`
  -- `B = 2*C` with `C` odd gives RHS `5 : ZMod 16`, impossible for a square
  sorry

/-- The halved factors in the even case. -/
def M_even (r B s : ℕ) : ℕ :=
  (2 * r ^ 2 + B ^ 2 - 2 * s) / 4

def N_even (r B s : ℕ) : ℕ :=
  (2 * r ^ 2 + B ^ 2 + 2 * s) / 4

lemma MN_even_product
    {r B s : ℕ} (hsol : QuarticSol r B s) (h4 : 4 ∣ B) :
    M_even r B s * N_even r B s = 5 * (B / 2) ^ 4 := by
  -- arithmetic from `(2r^2+B^2)^2-(2s)^2=5B^4`
  -- use `ring_nf` after moving to `ℤ` if Nat subtraction is annoying
  sorry

lemma MN_even_coprime
    {r B s : ℕ} (hsol : QuarticSol r B s) (h4 : 4 ∣ B) :
    Nat.Coprime (M_even r B s) (N_even r B s) := by
  -- use `M+N = r^2+B^2/2`, `N-M=s`, and the prime-divisor argument above
  sorry

/-- Coprime factors of `5*C^4` are fourth powers, with the unique factor `5` on one side. -/
lemma coprime_mul_eq_five_fourth_split
    {M N C : ℕ} (hcop : Nat.Coprime M N)
    (hMN : M * N = 5 * C ^ 4) :
    ∃ a b : ℕ,
      C = a * b ∧ Nat.Coprime a b ∧
        ((M = a ^ 4 ∧ N = 5 * b ^ 4) ∨
         (M = 5 * a ^ 4 ∧ N = b ^ 4)) := by
  -- best proved by `Nat.factorization` / prime exponents
  sorry

/-- Primitive Pythagorean parametrization plus square-product extraction. -/
lemma primitive_pythagorean_square_leg_descent
    {A b r : ℕ}
    (hprim : Nat.Coprime A (2 * b ^ 2))
    (heq : A ^ 2 + (2 * b ^ 2) ^ 2 = r ^ 2) :
    ∃ x y : ℕ,
      0 < x ∧ 0 < y ∧ b = x * y ∧
      (A = x ^ 4 - y ^ 4 ∨ A = y ^ 4 - x ^ 4) := by
  -- use the existing primitive Pythagorean triple parametrization if available;
  -- otherwise prove/import it once and reuse it.
  sorry

lemma quartic_even_descent
    {r B s : ℕ} :
    QuarticSol r B s → Even B →
    ∃ r' B' s' : ℕ,
      QuarticSol r' B' s' ∧ Even B' ∧ B' < B := by
  intro hsol hBeven
  have h4 : 4 ∣ B := quartic_not_two_mod_four hsol hBeven
  let M := M_even r B s
  let N := N_even r B s
  have hMN : M * N = 5 * (B / 2) ^ 4 := MN_even_product hsol h4
  have hcopMN : Nat.Coprime M N := MN_even_coprime hsol h4
  obtain ⟨a, b, hC, habcop, hsplit⟩ :=
    coprime_mul_eq_five_fourth_split hcopMN hMN
  -- Case split on `hsplit`; each branch produces a primitive Pythagorean triple,
  -- then a smaller even quartic solution as above.
  sorry

end FLT.C20
```

That is the right dependency structure.  The hard lemmas are reusable and local.  The final `quartic_B_odd` proof is then tiny.

## Important implementation warning: use `ℤ` for the algebra steps

The equation contains subtraction:

```lean
s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4
```

If your variables are `ℕ`, this is truncated subtraction.  For the factorization identities, it is much safer to cast to `ℤ` and do:

```lean
have hZ : (s : ℤ) ^ 2 = (r : ℤ) ^ 4 + (r : ℤ) ^ 2 * (B : ℤ) ^ 2 - (B : ℤ) ^ 4 := by
  exact_mod_cast heq

have hfactor :
    ((2 * (r : ℤ)^2 + (B : ℤ)^2) - 2 * (s : ℤ)) *
    ((2 * (r : ℤ)^2 + (B : ℤ)^2) + 2 * (s : ℤ)) =
      5 * (B : ℤ)^4 := by
  nlinarith [hZ]
```

Then prove positivity of the factors and move back to `ℕ`.  This avoids fighting `Nat.sub`.

## Bottom line

The replacement for the failed mod proof is:

```text
B even
⇒ 4 ∣ B
⇒ define M,N by dividing the two Pell-type factors by 4
⇒ split coprime factors of 5*(B/2)^4
⇒ primitive Pythagorean parametrization
⇒ smaller primitive solution with even B'
⇒ infinite descent contradiction.
```

So `both_odd` should be obtained by this order:

1. prove `Odd B` using `quartic_even_descent` + strong induction/no-infinite-descent;
2. prove `Odd r` afterward by the easy mod-`4` argument from `Odd B` and `gcd(r,B)=1`.

Do **not** try to prove `B` odd from `rat_denom_square`; and do **not** try to finish the `4 ∣ B` case by congruences.  The `4 ∣ B` case is exactly where the descent lives.
