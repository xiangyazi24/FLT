# Q1268 (dm1): infinite descent for `s² = r⁴ + r²B² - B⁴`

## Statement to prove

The clean Lean statement should avoid natural-number subtraction by writing the equation as

```text
s² + B⁴ = r⁴ + r² B².
```

Equivalently, over integers:

```text
s² = r⁴ + r² B² - B⁴.
```

The theorem is:

```text
If r > 0, B > 0, gcd(r,B)=1, and s² = r⁴ + r²B² - B⁴,
then r = B = 1 and s = ±1.
```

For a Nat-valued formalization, the conclusion is `r = 1 ∧ B = 1 ∧ s = 1` if `s : ℕ`. For an integer `s`, the conclusion is `r = 1 ∧ B = 1 ∧ s^2 = 1`, or equivalently `s = 1 ∨ s = -1`.

The descent measure is `B`.

## Normalization

Because the equation only involves `s²`, replace `s` by `|s|`. So assume `s ≥ 0`.

Define

```text
A = 2r² + B²,
U = A - 2s,
V = A + 2s.
```

Then your factorization is

```text
U V = 5 B⁴.
```

Indeed,

```text
(A - 2s)(A + 2s)
  = A² - 4s²
  = (2r² + B²)² - 4(r⁴ + r²B² - B⁴)
  = 5B⁴.
```

Assume, as you said you have already proved, that

```text
U > 0,
V > 0,
gcd(U,V) = 1,
U and V are odd.
```

Also `s ≠ 0`, because if `s = 0`, then `U = V`, contradicting `gcd(U,V)=1` and `UV=5B⁴>1`. Thus, after replacing `s` by `|s|`,

```text
0 < U < V.
```

We will use the equations

```text
U + V = 2A = 4r² + 2B²,
V - U = 4s.
```

## Splitting lemma for coprime factors of `5B⁴`

The main arithmetic splitting lemma is:

```text
If U V = 5B⁴, gcd(U,V)=1, U,V > 0, and U,V are odd,
then there exist positive coprime odd integers a,b with B = ab such that exactly one of the following holds:

  Case I:  U = a⁴  and V = 5b⁴;
  Case II: U = 5a⁴ and V = b⁴.
```

This is the exact formal content of “every splitting of `5B⁴` into coprime odd factors.”

### Proof of the splitting lemma

Use prime valuations.

For every prime `p`, since `gcd(U,V)=1`, all of the `p`-adic valuation of `UV` lies in exactly one of `U` or `V`.

For `p ≠ 5`,

```text
v_p(UV) = v_p(5B⁴) = 4 v_p(B),
```

so the exponent of `p` in whichever factor contains it is a multiple of `4`.

For `p = 5`,

```text
v_5(UV) = v_5(5B⁴) = 1 + 4 v_5(B),
```

so exactly one of `U,V` has `5`-adic valuation congruent to `1 mod 4`; the other has `5`-adic valuation congruent to `0 mod 4`.

Therefore the factor carrying the extra `5` is `5` times a fourth power, and the other factor is a fourth power. Because the prime supports of `U` and `V` are disjoint, the fourth-root parts are coprime; call them `a` and `b`. Then `B=ab`.

Since `U,V` are odd, both `a,b` are odd.

### Lean shape

Use `Nat.factorization` or `padicValNat`. The clean lemma target is:

```lean
-- Schematic target; use your local positivity/coprime predicates.
lemma coprime_odd_factorization_five_mul_fourth
    {U V B : ℕ}
    (hU : 0 < U) (hV : 0 < V)
    (hcop : Nat.Coprime U V)
    (hoddU : Odd U) (hoddV : Odd V)
    (hprod : U * V = 5 * B^4) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ Odd a ∧ Odd b ∧ Nat.Coprime a b ∧ B = a*b ∧
        ((U = a^4 ∧ V = 5*b^4) ∨ (U = 5*a^4 ∧ V = b^4)) :=
  -- prove by prime valuations
  -- no `sorry` in the final file
  by
    -- implementation target, not a completed proof here
    admit
```

## Primitive Pythagorean-square-leg lemma

The descent uses one standard lemma, which should be proved once and reused.

### Lemma

Suppose

```text
h² + y⁴ = z²,
```

with

```text
h > 0,
y > 0,
gcd(h,y)=1,
h even,
y odd.
```

Then there exist coprime positive odd integers `u < v` such that

```text
y = uv,
2h = v⁴ - u⁴.
```

### Proof

The triple

```text
h² + (y²)² = z²
```

is a primitive Pythagorean triple: `gcd(h,y²)=1`, `h` is even, and `y²` is odd.

Therefore there are coprime integers `m > n > 0` of opposite parity such that

```text
h   = 2mn,
y²  = m² - n²,
z   = m² + n².
```

Factor

```text
y² = (m-n)(m+n).
```

The two factors `m-n` and `m+n` are coprime. Indeed any common divisor divides their sum `2m` and difference `2n`; since `gcd(m,n)=1` and both `m±n` are odd, the common divisor is `1`.

Since their product is a square and they are coprime, each is a square:

```text
m-n = u²,
m+n = v²,
```

with `u,v` positive odd, coprime, and `u < v`.

Then

```text
y² = u²v²,
```

so `y=uv`, and

```text
2h = 4mn = (m+n)² - (m-n)² = v⁴ - u⁴.
```

### Lean shape

```lean
-- Schematic target.
lemma primitive_pythagorean_square_odd_leg
    {h y z : ℕ}
    (hh : 0 < h) (hy : 0 < y)
    (hcop : Nat.Coprime h y)
    (heven : Even h) (hodd : Odd y)
    (heq : h^2 + y^4 = z^2) :
    ∃ u v : ℕ,
      0 < u ∧ u < v ∧ Odd u ∧ Odd v ∧ Nat.Coprime u v ∧
      y = u*v ∧ 2*h = v^4 - u^4 :=
  -- use primitive Pythagorean triples, then split coprime square factors
  by
    admit
```

If subtraction in `2*h = v^4 - u^4` is inconvenient over `ℕ`, state it as

```lean
2*h + u^4 = v^4
```

which is better for Lean.

## Descent from the splitting: Case I

Assume the splitting is

```text
U = a⁴,
V = 5b⁴,
B = ab,
gcd(a,b)=1,
a,b odd.
```

Using `U+V = 4r² + 2B²`, we get

```text
a⁴ + 5b⁴ = 4r² + 2a²b².
```

Rearrange:

```text
4r² = a⁴ - 2a²b² + 5b⁴
    = (a² - b²)² + 4b⁴.
```

Thus

```text
r² = ((a² - b²)/2)² + b⁴.
```

Because `a,b` are odd, `a²-b²` is divisible by `8`, so

```text
h = |a²-b²| / 2
```

is a positive even integer unless `a=b`.

Also

```text
gcd(h,b)=1.
```

Proof: if a prime divides both `h` and `b`, then because `b` is odd it divides `2h = |a²-b²|`, hence it divides `a²`, hence it divides `a`, contradicting `gcd(a,b)=1`.

So, if `a ≠ b`, the Pythagorean-square-leg lemma applied to

```text
h² + b⁴ = r²
```

gives coprime positive odd `u < v` with

```text
b = uv,
2h = v⁴ - u⁴.
```

Since `2h = |a²-b²|`, there are two subcases.

### Case I.0: `a = b`

Since `gcd(a,b)=1`, this gives

```text
a = b = 1.
```

Then

```text
B = ab = 1.
```

From

```text
U+V = 1 + 5 = 6 = 4r² + 2B² = 4r² + 2,
```

we get

```text
r² = 1,
```

hence

```text
r = 1.
```

This is exactly the base solution.

### Case I.1: `a > b`

Here

```text
a² - b² = v⁴ - u⁴.
```

Since `b=uv`, we have

```text
a² = b² + v⁴ - u⁴
   = u²v² + v⁴ - u⁴
   = v⁴ + v²u² - u⁴.
```

Therefore

```text
(s', r', B') = (a, v, u)
```

is a new primitive solution:

```text
s'² = r'⁴ + r'² B'² - B'⁴.
```

Primitivity follows from `gcd(u,v)=1`.

The new `B'` is smaller:

```text
B' = u < uv = b ≤ ab = B.
```

So any non-base solution in this subcase descends to a smaller one.

### Case I.2: `a < b`

Here

```text
b² - a² = v⁴ - u⁴.
```

Since `b=uv`, we have

```text
a² = b² - (v⁴ - u⁴)
   = u²v² - v⁴ + u⁴
   = u⁴ + u²v² - v⁴.
```

Therefore

```text
(s', r', B') = (a, u, v)
```

is a new primitive solution:

```text
s'² = r'⁴ + r'² B'² - B'⁴.
```

Again primitivity follows from `gcd(u,v)=1`.

We must check that `B' = v < B`. Since `b=uv`, it is enough to know `u > 1`; then

```text
v < uv = b ≤ ab = B.
```

Why is `u > 1`? If `u=1`, then

```text
a² = 1 + v² - v⁴.
```

But `u < v` and both are positive odd, so `v ≥ 3`, and then

```text
1 + v² - v⁴ < 0,
```

impossible for a square. Hence `u > 1`, and the descent is strict.

## Descent from the splitting: Case II

Assume the splitting is

```text
U = 5a⁴,
V = b⁴,
B = ab,
gcd(a,b)=1,
a,b odd.
```

Since `U < V`, we have

```text
5a⁴ < b⁴,
```

hence in particular

```text
a < b.
```

Using `U+V = 4r² + 2B²`, we get

```text
5a⁴ + b⁴ = 4r² + 2a²b².
```

Rearrange:

```text
4r² = b⁴ - 2a²b² + 5a⁴
    = (b² - a²)² + 4a⁴.
```

Thus

```text
r² = ((b² - a²)/2)² + a⁴.
```

Set

```text
h = (b² - a²)/2.
```

Because `a,b` are odd, `h` is even. Since `a<b`, `h>0`. As above,

```text
gcd(h,a)=1.
```

Apply the Pythagorean-square-leg lemma to

```text
h² + a⁴ = r².
```

We get coprime positive odd `u < v` such that

```text
a = uv,
2h = v⁴ - u⁴.
```

Since `2h = b² - a²`, we get

```text
b² - a² = v⁴ - u⁴.
```

Using `a=uv`,

```text
b² = a² + v⁴ - u⁴
   = u²v² + v⁴ - u⁴
   = v⁴ + v²u² - u⁴.
```

Therefore

```text
(s', r', B') = (b, v, u)
```

is a new primitive solution:

```text
s'² = r'⁴ + r'² B'² - B'⁴.
```

The new `B'` is strictly smaller:

```text
B' = u < uv = a ≤ ab = B.
```

Thus Case II always descends.

## Infinite descent conclusion

Now prove the theorem by minimal counterexample on `B`.

Assume there is a primitive positive solution with not `(r=B=1)`. Choose one with minimal positive `B`.

Construct `U,V`. By the splitting lemma, either Case I or Case II holds.

* In Case I.0, `a=b=1`, hence `B=1` and `r=1`, contradicting that the solution was non-base.
* In Case I.1, we construct a new primitive solution with `B' = u < B`.
* In Case I.2, we construct a new primitive solution with `B' = v < B`.
* In Case II, we construct a new primitive solution with `B' = u < B`.

Every non-base case contradicts the minimality of `B`. Therefore there is no non-base primitive positive solution.

Hence every primitive positive solution has

```text
r = 1,
B = 1.
```

Substituting into the equation gives

```text
s² = 1,
```

so over integers

```text
s = ±1,
```

and over naturals

```text
s = 1.
```

## Lean formalization plan

The final proof should be organized into small lemmas with the descent step as the core.

### Suggested Nat predicate

Use the subtraction-free equation.

```lean
import Mathlib

noncomputable section

/-- Primitive positive solutions to `s² = r⁴ + r²B² - B⁴`, written without subtraction. -/
def IsSolution (r B s : ℕ) : Prop :=
  0 < r ∧ 0 < B ∧ Nat.Coprime r B ∧ s^2 + B^4 = r^4 + r^2 * B^2
```

### Splitting lemma target

```lean
lemma coprime_odd_factorization_five_mul_fourth
    {U V B : ℕ}
    (hU : 0 < U) (hV : 0 < V)
    (hcop : Nat.Coprime U V)
    (hoddU : Odd U) (hoddV : Odd V)
    (hprod : U * V = 5 * B^4) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ Odd a ∧ Odd b ∧ Nat.Coprime a b ∧ B = a*b ∧
        ((U = a^4 ∧ V = 5*b^4) ∨ (U = 5*a^4 ∧ V = b^4)) := by
  -- prime factorization / valuations
  sorry
```

### Pythagorean-square-leg lemma target

State subtraction-free:

```lean
lemma primitive_pythagorean_square_odd_leg
    {h y z : ℕ}
    (hh : 0 < h) (hy : 0 < y)
    (hcop : Nat.Coprime h y)
    (heven : Even h) (hodd : Odd y)
    (heq : h^2 + y^4 = z^2) :
    ∃ u v : ℕ,
      0 < u ∧ u < v ∧ Odd u ∧ Odd v ∧ Nat.Coprime u v ∧
      y = u*v ∧ 2*h + u^4 = v^4 := by
  -- primitive Pythagorean triple plus coprime factors of a square
  sorry
```

### Descent-step theorem target

This is the most important lemma. Once it is proved, the infinite descent is routine.

```lean
/-- Every non-base primitive solution produces a smaller primitive solution. -/
lemma descent_step
    {r B s : ℕ}
    (hsol : IsSolution r B s)
    (hnot : ¬ (r = 1 ∧ B = 1)) :
    ∃ r' B' s' : ℕ, IsSolution r' B' s' ∧ B' < B := by
  -- 1. Define A,U,V.
  -- 2. Use your already-proved positivity/coprime/odd factor lemmas for U,V.
  -- 3. Apply `coprime_odd_factorization_five_mul_fourth`.
  -- 4. Case I: U=a^4, V=5*b^4.
  --    * If a=b, prove base, contradict `hnot`.
  --    * If a>b, apply `primitive_pythagorean_square_odd_leg` to `h= (a^2-b^2)/2`, `y=b`.
  --      Return `(r',B',s')=(v,u,a)`.
  --    * If a<b, apply it to `h= (b^2-a^2)/2`, `y=b`.
  --      Return `(r',B',s')=(u,v,a)` and prove `u>1` to get `v<B`.
  -- 5. Case II: U=5*a^4, V=b^4.
  --    Use `U<V` to get `a<b`, apply the square-leg lemma to `h=(b^2-a^2)/2`, `y=a`.
  --    Return `(r',B',s')=(v,u,b)`.
  sorry
```

### Infinite descent theorem target

Use well-founded induction on `B`.

```lean
theorem solution_eq_one
    {r B s : ℕ} (hsol : IsSolution r B s) :
    r = 1 ∧ B = 1 ∧ s = 1 := by
  classical
  -- Strong induction on B.
  -- Inductive hypothesis: all solutions with smaller B are base.
  -- If current solution is non-base, `descent_step` gives a smaller solution, contradiction.
  -- Once r=B=1, the equation gives `s^2 + 1 = 2`, hence `s=1`.
  sorry
```

The `sorry`s above mark proof obligations to implement; they are not new assumptions. The mathematical descent is complete once the three lemmas are filled.

## Checklist of arithmetic facts needed in Lean

1. `a,b` odd implies `a²-b²` is divisible by `8`, so `|a²-b²|/2` is even.
2. `Nat.Coprime a b` implies `Nat.Coprime ((|a²-b²|)/2) b`, when `a,b` are odd and unequal.
3. Primitive Pythagorean parametrization for `h² + y⁴ = z²` with `h` even, `y` odd.
4. If coprime positive integers multiply to a square, each is a square.
5. If `u=1`, `u<v`, and `v` is odd, then `1 + v² < v⁴`; this rules out the Case I.2 edge case.
6. Strict descent inequalities:

```text
Case I.1:  u < uv = b ≤ ab = B.
Case I.2:  v < uv = b ≤ ab = B, using u > 1.
Case II:   u < uv = a ≤ ab = B.
```

## Final mathematical conclusion

The factor splitting has exactly one base branch and three descent branches:

```text
U=a⁴, V=5b⁴, a=b  -> r=B=1.
U=a⁴, V=5b⁴, a>b -> smaller solution (v,u,a).
U=a⁴, V=5b⁴, a<b -> smaller solution (u,v,a).
U=5a⁴,V=b⁴       -> smaller solution (v,u,b).
```

Thus a minimal non-base solution cannot exist. Therefore the only primitive positive solution is

```text
r = B = 1,
```

with

```text
s² = 1.
```
