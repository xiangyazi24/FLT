from sage.all import *
import time

p = 11
k = GF(p)
print("Q3976_CANONICAL_FIELD", p, flush=True)


def tmark(label, t0):
    print(label, "SECONDS", RR(time.time()-t0), flush=True)
    return time.time()


def tate_field(k):
    Kv = FunctionField(k, 'v')
    v = Kv.gen()
    Pc = PolynomialRing(Kv, 'c')
    c = Pc.gen()
    b = c+c^2*v
    F5 = b-c
    F6 = b-c-c^2
    F7 = c^3-b^2+b*c
    F8 = 2*b^2-3*b*c-b*c^2+c^2
    F9 = F5^3+c^3*F6
    G11 = F7*F5^3-b*c*F6^3
    G12 = c*F6*(F5^2*F8+F7^2)
    G13 = F5*F7^3+b*c*F6^3*F8
    G14 = F7*(b*F6^2*F9-c^2*F5*F8^2)
    sub25 = (G11*G13^3-b*G14*G12^3)//F5
    E = sub25//c^40
    print("TATE_POLY", E.degree(), len(E.list()), flush=True)
    return Kv.extension(E.monic(), 'ct')


def lmfdb_field(k):
    KC = FunctionField(k, 'C')
    C = KC.gen()
    PW = PolynomialRing(KC, 'W')
    W = PW.gen()
    H = (C^3*W^8+2*C^2*W^9+C*W^10
       +C^4*W^6+3*C^3*W^7+2*C^2*W^8
       -C^4*W^5-2*C^3*W^6+C*W^8
       -C^5*W^3-3*C^4*W^4+C^3*W^5+2*C^2*W^6-2*C*W^7-W^8
       +C^4*W^3-C^3*W^4-4*C^2*W^5-C*W^6
       -2*C^4*W^2-C^3*W^3+2*C^2*W^4-C*W^5
       +C^4*W+2*C^3*W^2-2*C^2*W^3+C*W^4
       -C^3*W+2*C^2*W^2+C^3)
    print("LMFDB_POLY", H.degree(), len(H.list()), flush=True)
    return KC.extension(H.monic(), 'wl')


def holomorphic_basis(F, tag):
    t0 = time.time()
    g = F.genus()
    t0 = tmark(tag+"_GENUS_"+str(g), t0)
    D0 = F.divisor_group().zero()
    B = D0.basis_differential_space()
    t0 = tmark(tag+"_DIFF_DIM_"+str(len(B)), t0)
    for i, w in enumerate(B):
        print(tag+"_OMEGA_"+str(i), w, flush=True)
    return B

start = time.time()
KT = tate_field(k)
tmark("TATE_BUILD", start)
BT = holomorphic_basis(KT, "TATE")

start = time.time()
KL = lmfdb_field(k)
tmark("LMFDB_BUILD", start)
BL = holomorphic_basis(KL, "LMFDB")

print("Q3976_CANONICAL_BASES_COMPLETE", flush=True)
