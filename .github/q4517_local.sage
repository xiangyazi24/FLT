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
    print('CURVE',name,'DISC',C.discriminant())
    for pname,P in [('P2',P2),('P3',P3)]:
        try:
            D=C.local_data(P)
            print('LOCAL_DATA',name,pname,D)
            for meth in ['kodaira_symbol','tamagawa_number','conductor_valuation','discriminant_valuation','minimal_model']:
                if hasattr(D,meth):
                    try: print(' LD',meth,getattr(D,meth)())
                    except Exception as ex: print(' LD_ERR',meth,repr(ex))
        except Exception as ex: print('LOCAL_DATA_ERR',name,pname,repr(ex))
try:
    Em=E.global_minimal_model()
    print('E_GMIN',Em.a_invariants(),Em.discriminant())
    print('E_TO_GMIN',E.isomorphism_to(Em),E.isomorphism_to(Em).tuple(),E.isomorphism_to(Em).rational_maps())
except Exception as ex: print('E_GMIN_ERR',repr(ex))
try:
    Epm=Ep.global_minimal_model()
    print('EP_GMIN',Epm.a_invariants(),Epm.discriminant())
    print('EP_TO_GMIN',Ep.isomorphism_to(Epm),Ep.isomorphism_to(Epm).tuple(),Ep.isomorphism_to(Epm).rational_maps())
except Exception as ex: print('EP_GMIN_ERR',repr(ex))
for n in [1,2,3,4,5]:
    try:
        Q,red=OK.quotient(P3^n,'r')
        print('QUOT',n,Q,'CARD',Q.cardinality(),'RED_A',red(OK(a)),'RED_PI',red(OK(a-1)))
        if n==5:
            els=list(Q)
            units=[x for x in els if x.is_unit()]
            cubes=set(x^3 for x in units)
            print('P3MOD5_COUNTS',len(els),len(units),len(cubes),len(units)//len(cubes))
            ba=red(OK(a)); bb=red(OK(a+1)); b2=red(OK(2))
            reps={}
            for i in range(3):
              for j in range(3):
                for k in range(3):
                  rr=ba^i*bb^j*b2^k
                  reps[(i,j,k)]=rr
            distinct=True
            for c1,r1 in reps.items():
              for c2,r2 in reps.items():
                if c1!=c2 and r1/r2 in cubes: distinct=False
            print('UNIT_BASIS_27_DISTINCT',distinct)
            covered=all(any(x/r in cubes for r in reps.values()) for x in units)
            print('UNIT_BASIS_COVERS',covered)
    except Exception as ex: print('QUOT_ERR',n,repr(ex))
try:
    F8,red2=OK.quotient(P2,'b')
    print('P2_RES',F8,F8.cardinality(),red2(OK(a)))
    units=[x for x in F8 if x!=0]
    print('P2_CUBE_BIJECTIVE',len(set(x^3 for x in units)),len(units))
except Exception as ex: print('P2_RES_ERR',repr(ex))
print('LOCAL_END')