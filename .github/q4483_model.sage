G=GammaH(25,[1,7,18,24])
S=CuspForms(G,2)
print('MODEL_BEGIN')
print('DIM',S.dimension())
B=S.q_expansion_basis(100)
BB=list(B)
PR=PolynomialRing(QQ,4,names=('z0','z1','z2','z3'))
z=PR.gens()
def mons_deg(d):
    return list(PR.monomials_of_degree(d))
def evalmon(m):
    out=BB[0].parent()(1)
    for i,e in enumerate(m.exponents()[0]):
        out *= BB[i]**e
    return out
def relation_space(d):
    mons=mons_deg(d)
    vals=[evalmon(m) for m in mons]
    M=matrix(QQ,100,len(mons),lambda n,j: vals[j][n])
    return mons,M.right_kernel()
mons2,K2=relation_space(2)
print('REL_DIM_2',K2.dimension())
quadrics=[]
for v in K2.basis():
    q=sum(v[j]*mons2[j] for j in range(len(mons2)))
    quadrics.append(q)
    print('QUADRIC',q)
mons3,K3=relation_space(3)
print('REL_DIM_3',K3.dimension())
cubics=[sum(v[j]*mons3[j] for j in range(len(mons3))) for v in K3.basis()]
# Find a cubic outside the span of z_i*Q.
if quadrics:
    q=quadrics[0]
    mults=[z[i]*q for i in range(4)]
    mon_index={m:i for i,m in enumerate(mons3)}
    def vec(poly):
        return vector(QQ,[poly.monomial_coefficient(m) for m in mons3])
    Mmult=matrix(QQ,[vec(p) for p in mults])
    for c in cubics:
        if Mmult.stack(matrix(QQ,[vec(c)])).rank() > Mmult.rank():
            print('CUBIC_NEW',c)
            break
try:
    M=ModularSymbols(G,2,sign=0).cuspidal_subspace()
    print('DIAMOND_METHODS',[s for s in dir(M) if 'diamond' in s.lower()])
    for a in [2,3,4,6,7,11]:
        for meth in ['diamond_bracket_matrix','diamond_bracket_operator']:
            if hasattr(M,meth):
                try: print('DIAMOND',a,meth,getattr(M,meth)(a))
                except Exception as e: print('DIAMOND_ERR',a,meth,repr(e))
except Exception as e: print('MS_ERR',repr(e))
print('MODEL_END')
