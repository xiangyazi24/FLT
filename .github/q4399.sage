from sage.all import *

print('Q4399_BEGIN')
R0.<Avar> = PolynomialRing(QQ)
L.<a> = NumberField(Avar^3 - 3*Avar - 1)
R.<z> = PolynomialRing(L)
A0 = -a - 1
q0 = a^2 - 1
rp = A0 + q0
rm = A0 - q0
x_of_z = (z*rm - rp)/(z - 1)

def fpoly(x):
    return x^6 + 4*x^5 + 10*x^4 + 10*x^3 + 5*x^2 + 2*x + 1

Fz = R((z-1)^6 * fpoly(x_of_z))
print('A0=',A0)
print('q0=',q0)
print('rplus=',rp)
print('rminus=',rm)
print('Fz=',Fz)
print('Fz_coeffs=',[Fz[i] for i in range(7)])
assert all(Fz[i] == 0 for i in [1,3,5])

c0 = Fz[0]; c1 = Fz[2]; c2 = Fz[4]; c3 = Fz[6]
print('C0=',c0)
print('C1=',c1)
print('C2=',c2)
print('C3=',c3)

# E+ from v^2 = c3*u^3 + c2*u^2 + c1*u + c0,
# via X=c3*u, Y=c3*v.
Eplus = EllipticCurve(L,[0,c2,0,c1*c3,c0*c3^2])
# E- from V^2=u*(c3*u^3+c2*u^2+c1*u+c0),
# via U=1/u,W=V/u^2 then X=c0*U,Y=c0*W.
Eminus = EllipticCurve(L,[0,c1,0,c2*c0,c3*c0^2])
E0Q = EllipticCurve(QQ,[1,-1,1,-5,5])
E0 = E0Q.change_ring(L)
print('EPLUS_AINVS=',Eplus.a_invariants())
print('EMINUS_AINVS=',Eminus.a_invariants())
print('E0_AINVS=',E0.a_invariants())
print('EPLUS_DISC=',Eplus.discriminant())
print('EMINUS_DISC=',Eminus.discriminant())
print('E0_DISC=',E0.discriminant())
print('EPLUS_J=',Eplus.j_invariant())
print('EMINUS_J=',Eminus.j_invariant())
print('E0_J=',E0.j_invariant())
print('PLUS_ISO_E0=',Eplus.is_isomorphic(E0))
print('MINUS_ISO_E0=',Eminus.is_isomorphic(E0))

# rational 3-isogenies of E0/Q
phis = E0Q.isogenies_prime_degree(3)
print('NUM_3ISOG=',len(phis))
for i,phiQ in enumerate(phis):
    EhatQ = phiQ.codomain()
    Ehat = EhatQ.change_ring(L)
    print('PHI',i,'EHATQ_AINVS=',EhatQ.a_invariants(),'EHATQ_LABEL=',getattr(EhatQ,'label',lambda:None)())
    print('PHI',i,'EHATQ_J=',EhatQ.j_invariant())
    print('PLUS_ISO_EHAT=',Eplus.is_isomorphic(Ehat))
    print('MINUS_ISO_EHAT=',Eminus.is_isomorphic(Ehat))
    try:
        print('PHI_MAP=',phiQ.rational_maps())
    except Exception as e:
        print('PHI_MAP_ERR=',repr(e))

# Find target isomorphisms and print exact maps.
def dump_iso(name, Efrom, Eto):
    print(name,'TRY')
    try:
        iso = Efrom.isomorphism_to(Eto)
        print(name,'OBJ=',iso)
        try: print(name,'TUPLE=',iso.tuple())
        except Exception as e: print(name,'TUPLE_ERR=',repr(e))
        try: print(name,'MAPS=',iso.rational_maps())
        except Exception as e: print(name,'MAPS_ERR=',repr(e))
        try:
            inv=~iso
            print(name,'INV_OBJ=',inv)
            print(name,'INV_MAPS=',inv.rational_maps())
        except Exception as e: print(name,'INV_ERR=',repr(e))
        return iso
    except Exception as e:
        print(name,'FAIL=',repr(e))
        return None

iso_plus_E0 = dump_iso('ISO_PLUS_E0',Eplus,E0)
iso_minus_E0 = dump_iso('ISO_MINUS_E0',Eminus,E0)
for i,phiQ in enumerate(phis):
    Ehat=phiQ.codomain().change_ring(L)
    dump_iso('ISO_PLUS_EHAT_%s'%i,Eplus,Ehat)
    dump_iso('ISO_MINUS_EHAT_%s'%i,Eminus,Ehat)

# Verify sigma action in z,Y coordinates.
sx = (A0*x_of_z - a)/(x_of_z - A0)
print('SIGMA_Z_CHECK=',R((sx-rp)/(sx-rm) + z))
# y multiplier expressed in z
mu = q0^3/(x_of_z-A0)^3
print('SIGMA_Y_MULT=',mu)
print('Q4399_END')
