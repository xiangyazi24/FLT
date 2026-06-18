# ChatGPT Drop File (dm2)

## Question

For

```text
E  : y² = x³ + x² - x
E' : Y² = X³ - 2X² + 5X,
```

with the 2-isogeny

```text
φ  : E  → E'
φ̂ : E' → E,
```

we have explicit descent data

```text
Sel^φ    = {1, -1}
Sel^φ̂   = {1, 5}.
```

The question is whether the two explicit descents together can force `x(P)` to be integral directly, without passing through the abstract rank-zero statement.

## 1. The dual prime-support trick

The dual cover is

```text
d*W² = d²*T⁴ - 2*d*T²*S² + 5*S⁴.
```

For a prime `p ∣ d`, reducing modulo `p` gives

```text
0 = 5*S⁴ mod p.
```

So if `p ≠ 5` and `p ∤ S`, contradiction.  Therefore the simple one-line argument works provided the cover solution is already normalized so that

```text
gcd(S,d) = 1.
```

With that primitive condition, the conclusion is:

```text
p ∣ d  →  p = 5.
```

So the dual analogue of `cover_forces_unit` is not literally “unit”; it is:

```text
cover_forces_five_unit:
  every prime divisor of d divides 5.
```

Equivalently, for squarefree `d`, the only possible prime support is `{5}`.  This gives

```text
d ∈ {±1, ±5}
```

before imposing the real/local sign conditions.  Then the real obstruction removes the negative classes:

```text
d = -1 :  -W² = T⁴ + 2T²S² + 5S⁴,
d = -5 :  -5W² = 25T⁴ + 10T²S² + 5S⁴,
```

which have no nontrivial real/rational solutions.  Thus the dual Selmer candidates reduce to

```text
{1, 5}.
```

If `gcd(S,d)=1` is not already part of the cover construction, then one needs a primitive-solution normalization lemma.  The usual argument is still elementary: if `p ∣ d` and `p ∣ S`, then the equation forces `p ∣ W`, and then another reduction forces `p ∣ T`, contradicting primitivity.  But the cleanest formal interface is to have the descent construction output a primitive solution with `gcd(S,d)=1` from the start.

## 2. The key obstruction to using both descents directly

For a point `P = (x,y) ∈ E(Q)` with `x ≠ 0`, the isogeny formula gives

```text
X(φ(P)) = y² / x².
```

Equivalently, using the curve equation,

```text
X(φ(P)) = x + 1 - 1/x = (x² + x - 1)/x = y²/x².
```

Therefore `X(φ(P))` is automatically a rational square.

So the dual descent value of `φ(P)` is always trivial:

```text
α_{φ̂}(φ(P)) = 1.
```

This is not an accident; it is the concrete exactness statement

```text
image(φ) ⊆ kernel(dual descent map).
```

Thus the dual Selmer computation

```text
Sel^φ̂ = {1, 5}
```

does not add a new denominator constraint on a point that has already come from `E` and is then pushed forward by `φ`.  The second coordinate in the proposed pair

```text
P ↦ (α_φ(P), α_{φ̂}(φ(P)))
```

is always `1` for non-special `P`.

This means the two descents do **not** directly imply integrality by simply evaluating both descent maps on `P` and `φ(P)`.

## 3. Why `Sel^φ = {1,-1}` alone is not enough

The φ-side tells us that for a non-special rational point `P ∈ E(Q)`, the squareclass of `x(P)` lies in

```text
{1, -1}.
```

But that does not imply `x(P)` is an integer.  For example, a rational number can have squareclass `1` while being nonintegral:

```text
x = (s/q)²,    q ≥ 2.
```

Likewise it can have squareclass `-1` while being nonintegral:

```text
x = -(s/q)²,   q ≥ 2.
```

So after the φ-descent, the remaining problem is exactly a denominator problem in the allowed squareclasses.

For the positive squareclass case, write

```text
x = s²/q²,
q ≥ 2,
gcd(s,q)=1.
```

Then, after clearing denominators in

```text
y² = x³ + x² - x,
```

one obtains the quartic obstruction

```text
t² = s⁴ + s²*q² - q⁴.
```

For the negative squareclass case, write

```text
x = -s²/q²,
q ≥ 2,
gcd(s,q)=1.
```

Then one obtains the companion obstruction

```text
t² = -s⁴ + s²*q² + q⁴.
```

Thus the φ-descent reduces integrality to explicit denominator quartics.  The dual descent does not remove those denominator cases, because `φ(P)` has trivial dual descent class automatically.

## 4. Can both descents force integrality without rank?

There are two different meanings of “using both descents.”

### 4.1 Evaluating both descent maps on `P` and `φ(P)`

This does **not** force integrality.

The reason is exactly the identity

```text
X(φ(P)) = (y/x)².
```

So the dual descent value of `φ(P)` is always `1`.  It cannot distinguish integral from nonintegral `x(P)`.

In this sense, the answer is no: the two Selmer inclusions, used in this naive direct way, do not prove integrality.

### 4.2 Using both descents as explicit exactness / divisibility tools

There is a possible direct proof that avoids Galois cohomology, but it is not just a denominator argument.  It would be an explicit infinite descent on the Mordell-Weil group.

The rough shape is:

```text
α_φ(P) ∈ {1,-1}
α_{φ̂}(Q) ∈ {1,5}
```

plus explicit kernel/image criteria show that points in certain descent classes are images under `φ` or `φ̂`, possibly after adding the visible 2-torsion point.  Then one proves directly, using the explicit isogeny formulas, that a non-torsion point would be repeatedly divisible by `2` or by alternating isogenies, with decreasing height or denominator.  That gives a contradiction.

This can avoid formalizing `H¹(Q,E[φ])`, but it is still an abstract descent proof in another form: one must formalize explicit exactness statements for the isogenies and a height/denominator descent.  It is likely more work than proving the denominator quartics directly.

## 5. Recommended Lean route for integrality

For the specific goal

```text
∀ P ∈ E(Q), x(P) is integral,
```

the cleanest direct route is:

### Step A: φ-descent image

Formalize the concrete φ-descent map

```text
α_φ(P) = squareclass(x(P))
```

with the special values for `O` and `(0,0)`, and prove

```text
α_φ(P) ∈ {1, -1}.
```

This uses the explicit covers and the local obstructions for bad classes.

### Step B: denominator obstruction for the allowed classes

Prove:

```text
no_positive_squareclass_denominator:
  ¬ ∃ s q t : ℤ,
    2 ≤ q ∧ gcd(s,q)=1 ∧
    t² = s⁴ + s²*q² - q⁴.
```

and, if the negative squareclass is not already handled elsewhere,

```text
no_negative_squareclass_denominator:
  ¬ ∃ s q t : ℤ,
    2 ≤ q ∧ gcd(s,q)=1 ∧
    t² = -s⁴ + s²*q² + q⁴.
```

Then conclude:

```text
x(P) ∈ ℤ.
```

This route uses the φ-descent and explicit quartic obstructions.  It does not require the dual descent.

## 6. Recommended Lean route for rank zero

For rank zero, the dual descent is important.  But if the goal is to avoid cohomology, the better statement is not “both descents force integrality.”  Instead, use explicit quotient/image statements:

```text
E(Q)  / φ̂(E'(Q)) injects into Sel^φ,
E'(Q) / φ(E(Q))  injects into Sel^φ̂.
```

These injections can be implemented by direct descent maps and explicit covers, without constructing `H¹`.  Then prove exactness of the isogeny sequence directly using formulas for `φ` and `φ̂`.  This is enough to recover the usual rank bound.

But if the immediate target is only integrality and point classification, it is simpler to avoid the dual descent and rank formula:

```text
φ-descent image {1,-1}
  + denominator quartic obstruction
  → x(P) integral
  + integral point classification
  → finite point list
  → rank zero, if needed.
```

## Bottom line

The dual prime-support argument works, but with the expected modification:

```text
p ∣ d  →  p = 5,
```

assuming the dual cover solution is primitive with `gcd(S,d)=1`.

However, the φ and φ̂ descents do not directly force integrality by evaluating the dual descent on `φ(P)`, because

```text
X(φ(P)) = y²/x²
```

is always a square.  The dual descent is therefore trivial on points coming from `E` via `φ`.

So the minimal direct proof of integrality should be:

```text
φ-descent ⇒ squareclass(x) ∈ {1,-1}
allowed squareclass + nonintegral denominator ⇒ explicit quartic solution
quartic obstruction ⇒ contradiction.
```

This avoids Galois cohomology completely.  The dual descent is still useful for a rank-zero proof, but it does not by itself replace the denominator quartic argument for integrality.
