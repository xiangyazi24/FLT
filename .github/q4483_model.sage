G=GammaH(25,[1,7,18,24])
S=CuspForms(G,2)
print('MODEL_BEGIN')
print('DIM',S.dimension())
print('METHODS',[s for s in dir(S) if any(k in s.lower() for k in ['expansion','basis','diamond','hecke','modular'])][:120])
B=None
for meth,args in [('q_expansion_basis',(80,)),('q_integral_basis',(80,)),('basis',())]:
    if hasattr(S,meth):
        try:
            B=getattr(S,meth)(*args)
            print('BASIS_METHOD',meth,'LEN',len(B))
            print('BASIS',B)
            break
        except Exception as e: print('BASIS_ERR',meth,repr(e))
if B is not None:
    # Coerce basis elements to q-expansions when needed.
    BB=[]
    for f in B:
        try: q=f.q_expansion(80)
        except Exception:
            try: q=f.qexp(80)
            except Exception: q=f
        BB.append(q)
    PR=PolynomialRing(QQ,4,names='z')
    z=PR.gens()
    def mons_deg(d):
        return [m for m in PR.monomials_of_degree(d)]
    def evalmon(m):
        out=BB[0].parent()(1)
        for i,e in enumerate(m.exponents()[0]):
            out *= BB[i]**e
        return out
    for d in [2,3]:
        mons=mons_deg(d)
        vals=[evalmon(m) for m in mons]
        M=matrix(QQ,80,len(mons),lambda n,j: vals[j][n])
        K=M.right_kernel()
        print('REL_DIM',d,K.dimension())
        for v in K.basis():
            rel=sum(v[j]*mons[j] for j in range(len(mons)))
            print('REL',d,rel)
try:
    M=ModularSymbols(G,2,sign=0).cuspidal_subspace()
    print('MS_METHODS',[s for s in dir(M) if 'diamond' in s.lower()][:50])
    for a in [2,3,4,6,7,11]:
        for meth in ['diamond_bracket_matrix','diamond_bracket_operator']:
            if hasattr(M,meth):
                try: print('DIAMOND',a,meth,getattr(M,meth)(a))
                except Exception as e: print('DIAMOND_ERR',a,meth,repr(e))
except Exception as e: print('MS_ERR',repr(e))
print('MODEL_END')
