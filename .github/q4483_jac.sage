H4=[1,7,18,24]
print('JAC_BEGIN')
for expr,name in [(lambda:J1(25),'J1'),(lambda:JH(25,H4),'JH4')]:
    try:
        J=expr()
        print('OBJ',name,J,'DIM',J.dimension())
        print('METHODS',name,[s for s in dir(J) if any(k in s.lower() for k in ['cusp','tors','rank','decomp','newform','simple','lseries'])][:120])
        for meth in ['decomposition','newform_decomposition','cuspidal_subgroup','rational_cuspidal_subgroup','torsion_subgroup','rank','analytic_rank']:
            if hasattr(J,meth):
                try:
                    r=getattr(J,meth)()
                    print(name,meth,r)
                    if hasattr(r,'order'):
                        try: print(name,meth,'ORDER',r.order())
                        except Exception as e: print(name,meth,'ORDER_ERR',repr(e))
                except Exception as e: print(name,meth,'ERR',repr(e))
    except Exception as e: print('OBJ_ERR',name,repr(e))
print('JAC_END')
