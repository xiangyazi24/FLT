# R34 ACK and arbitrary ideal norm multiplicities

TASK_ID: FLT-N25-INFINITY-PRIME-NORMS
REVISION: 34
TYPE: ACK_AND_RESULT
STATUS: THREE-PRIME-NORMS-ACCEPTED; ARBITRARY-IDEAL-MULTIPLICITY-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the norm/valuation route

## Accepted source

R34 accepts N25F_InfinityCanonicalSeparable and N25F_InfinityPrimeNorms
byte-equal from our 4911cd7f7f80851fa693e03f1cef6ab90dbf07a3 delivery.
The exact source files were independently read back and compared. The lead
reports a successful build and all five public declarations standard-only.
The source and dispatch pins above were rechecked before this delivery.

## New result

Candidate: comms/candidates/N25F_InfinityNormMultiplicity.lean.
Four public declarations prove the prime case and extend it by actual
Dedekind ideal factorization to every nonzero normalization ideal:

    infinity_relNorm_multiplicity (I : Ideal InfinityNormalization) (hI : I ≠ ⊥) :
      (normalizedFactors (Ideal.relNorm BasePolynomial I)).count infinityBasePrime =
        (normalizedFactors I).count xInfinityPrime +
        (normalizedFactors I).count yzInfinityPrime +
        (normalizedFactors I).count zInfinityPrime

The off-fiber lemma uses the existing general theorem that a prime ideal's
relative norm is a power of its contraction. The actual prime case uses the
accepted three degree-one prime norms, pairwise distinctness, and complete
classification of primes above (T). It then discharges the generic prime
premise in the induction theorem. No new norm identity, perfectness,
separability, order compatibility or product-formula assumption is added to
the actual result. The candidate enables all named boundary Algebras locally.

## Validation ledger

PASS: generic off-fiber and factorization helpers, generic-01, exit 0,
5.960 seconds wrapper elapsed, peak child RSS 2,888,296 KiB; both audits
exactly [propext, Classical.choice, Quot.sound].

PASS: complete generic-family proof, family-02, exit 0, 5.724 seconds,
peak child RSS 2,891,872 KiB. All four public audits are exactly the standard
three, with no sorryAx or warnings. Its source SHA-256 is
81306f5b9eccb037497fe6596d7e8d130e268b1010d4110c8eabbff6bfe41e9d.
The attached generator transparently replaces the actual carriers, centers
and already accepted prime-norm/fiber facts by explicit family parameters.
The production specialization closes those facts with their accepted names.
family-01 also passed but had unused-simp warnings; family-02 is the clean
final checkpoint. These completed checks were not repeated for delivery.

NOT RUN locally: the full named FLT production import and its four audits.
ActualInfinityNormMultiplicityCheck.lean enumerates those declarations for
the lead. The family check does not verify the final named bindings in the
full FLT environment. No compiled FLT dependency bundle has been received.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Checks use one shared
gate per invocation, one CPU/thread, 3,072 MiB Lean cap, 60 active seconds,
and synthesis budget 200,000. Wrapper elapsed may include gate waiting.
The user's later explicit request for bounded local feedback supersedes the
older source-only build addendum; aggregate acceptance remains lead-owned.

## Next owned step and frontier

Next is the genuine local length/order equality with prime-factor count,
then its principal-function application. A separate generic two-lemma
candidate has an ordinary rewrite error in its first local check; it is
not included as checked evidence here. This packet does not wait for that
separate work. The field-norm conversion and comparison with the affine
norm-degree identity still follow afterward.

The general projective product formula, N25 and Mazur remain open. The last
fresh root closure still has no sorryAx and exactly the same three custom
axioms: no_prime_order_ge_23, CyclicExclusion25.no_explicit_order25_obstruction,
and CyclicExclusion49.no_raw_order49_tate_obstruction (all under MazurProof).

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-PRIME-NORMS-r34-manifest.json
