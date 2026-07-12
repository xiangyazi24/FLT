N = 25
units = [a for a in range(N) if gcd(a,N)==1]
Hs = [
  ('X1', [1,24]),
  ('H4', [1,7,18,24]),
  ('H10_X1_5', sorted(set([power_mod(4,i,25) for i in range(10)]))),
  ('X0', units),
]
print('Q4483_BEGIN')
for name,H in Hs:
    G=GammaH(N,H)
    print('GROUP',name,'H',H,'GENUS',G.genus(),'INDEX',G.index(),'CUSPS',G.ncusps(),'NU2',G.nu2(),'NU3',G.nu3())
    try:
        C=ModularSymbols(G,2,sign=0).cuspidal_subspace()
        print('CUSPIDAL_DIM',name,C.dimension())
        dec=C.decomposition()
        print('DECOMP',name,[(A.dimension(), [str(A.hecke_polynomial(p)) for p in [2,3,7] if gcd(p,N)==1]) for A in dec])
    except Exception as e:
        print('MODSYM_ERR',name,repr(e))
print('Q4483_END')
