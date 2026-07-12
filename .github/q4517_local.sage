Qx.<z> = PolynomialRing(QQ)
K.<a> = NumberField(z^3-3*z-1)
OK=K.ring_of_integers()
P2=K.ideal(2)
P3=K.ideal(a-1)
E=EllipticCurve(K,[1,-1,1,-5,5])
Ep=EllipticCurve(K,[-3,0,2,30,26])
Epin=EllipticCurve(K,[1,a^2+a-3,a^2+a-1,4-a^2,-a-2])
print('LOCAL_BEGIN')
for name,C in [('E',E),('EVELU',Ep),('EPIN',Epin)]:
    for pname,P in [('P2',P2),('P3',P3)]:
        try:
            D=C.local_data(P)
            print('LD',name,pname,'KOD',D.kodaira_symbol(),'C',D.tamagawa_number(),'FV',D.conductor_valuation(),'DV',D.discriminant_valuation(),'MIN',D.minimal_model().a_invariants())
        except Exception as ex: print('LD_ERR',name,pname,repr(ex))
for name,C in [('E',E),('EVELU',Ep)]:
    try:
        Cm=C.global_minimal_model()
        iso=C.isomorphism_to(Cm)
        print('GMIN',name,Cm.a_invariants(),Cm.discriminant(),'URST',iso.tuple(),'MAPS',iso.rational_maps())
    except Exception as ex: print('GMIN_ERR',name,repr(ex))
for n in [1,2,3,4,5]:
    try:
        Q,red=OK.quotient(P3^n,'r')
        print('QUOT',n,'CARD',Q.cardinality(),'A',red(OK(a)),'PI',red(OK(a-1)))
        if n==5:
            els=list(Q)
            units=[x for x in els if x.is_unit()]
            cubes=set(x^3 for x in units)
            print('P3MOD5_COUNTS',len(els),len(units),len(cubes),len(units)//len(cubes))
            ba=red(OK(a)); bb=red(OK(a+1)); b2=red(OK(2))
            reps={(i,j,k):ba^i*bb^j*b2^k for i in range(3) for j in range(3) for k in range(3)}
            distinct=all(c1==c2 or r1/r2 not in cubes for c1,r1 in reps.items() for c2,r2 in reps.items())
            covered=all(any(x/r in cubes for r in reps.values()) for x in units)
            print('UNIT_BASIS_27',distinct,covered)
    except Exception as ex: print('QUOT_ERR',n,repr(ex))
try:
    F8,red2=OK.quotient(P2,'b')
    units=[x for x in F8 if x!=0]
    print('P2_RES_CARD',F8.cardinality(),'A',red2(OK(a)),'CUBES',len(set(x^3 for x in units)),len(units))
except Exception as ex: print('P2_RES_ERR',repr(ex))
try:
    Eh=EllipticCurve(K,[1,-1,1,25,1])
    iso=Ep.isomorphism_to(Eh)
    print('EVELU_TO_EHAT_URST',iso.tuple(),'MAPS',iso.rational_maps())
except Exception as ex: print('EVELU_EHAT_ERR',repr(ex))
print('LOCAL_END')