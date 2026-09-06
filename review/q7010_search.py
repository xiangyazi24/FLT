#!/usr/bin/env python3
import math, time
import numpy as np

B = 10_000
Avals = np.arange(-B, B + 1, dtype=np.int64)
maxN = 71 * B**4
maxroot = int(maxN ** 0.2) + 10
while (maxroot + 1) ** 5 <= maxN:
    maxroot += 1
while maxroot ** 5 > maxN:
    maxroot -= 1
fifths = np.array([n**5 for n in range(maxroot + 1)], dtype=np.int64)
fifths25 = 25 * fifths[fifths <= maxN // 25]

def member_sorted(vals, arr):
    idx = np.searchsorted(arr, vals)
    ok = idx < len(arr)
    out = np.zeros(vals.shape, dtype=bool)
    ii = np.nonzero(ok)[0]
    out[ii] = arr[idx[ii]] == vals[ii]
    return out

def norm_array(a, b):
    # N_{Q(zeta_5)/Q}(a+b*s*zeta)
    return ((((a + 5*b) * a + 15*b*b) * a + 25*b**3) * a + 25*b**4)

t0 = time.time()
all_candidates = []
negative_candidates = []
for b in range(1, B + 1):
    N = norm_array(Avals, np.int64(b))
    m1 = member_sorted(N, fifths)
    m25 = member_sorted(N, fifths25)
    idxs = np.nonzero(m1 | m25)[0]
    for idx in idxs.tolist():
        a = int(Avals[idx]); n = int(N[idx])
        if math.gcd(a, b) != 1:
            continue
        # For a primitive pair the pi-adic exponent of alpha_0 is 2 exactly
        # in the branch 5|a, 5∤b, so its absolute norm must be 25 times a
        # fifth power.  In the other two branches v_pi(alpha_0)=0, so its
        # absolute norm must itself be a fifth power whenever W is globally
        # a fifth power (pairwise good-prime support + e_i != 0 mod 5).
        expected = m25[idx] if (a % 5 == 0 and b % 5 != 0) else m1[idx]
        if not expected:
            continue
        row = (a, b, n)
        all_candidates.append(row)
        if b % 5 == 0:
            negative_candidates.append(row)

elapsed = time.time() - t0
print(f"NUMPY_VERSION={np.__version__}")
print(f"BOUND={B}")
print(f"PAIR_DOMAIN=b=1..{B}, a=-{B}..{B}; sign-normalized b>0")
print(f"RAW_PAIRS={B*(2*B+1)}")
print(f"NORM_FILTER_SECONDS={elapsed:.3f}")
print(f"ALL_NORM_CANDIDATES={len(all_candidates)}")
print(f"NEGATIVE_BRANCH_NORM_CANDIDATES={len(negative_candidates)}")
print("NEGATIVE_BRANCH_NORM_CANDIDATE_LIST=", negative_candidates)
print("ALL_NORM_CANDIDATE_LIST=", all_candidates)
print("NOTE=every global W-fifth-power parameter in this box must occur in ALL_NORM_CANDIDATE_LIST; exact PARI rejection of that list is run by q7010_check.gp")
