\\ Q1094 exact 2-descent and analytic data for 17a1 and 19a1

print("PARI version = ", version());

E17 = ellinit([1,-1,1,-1,-14]);
E19 = ellinit([0,1,1,-9,-15]);

print("=== 17a1 ===");
print("disc = ", E17.disc);
print("j = ", E17.j);
print("tors = ", elltors(E17));
print("rank = ", ellrank(E17));
C17 = ell2cover(E17);
print("#ell2cover = ", #C17);
print("ell2cover raw = ", C17);
print("cover 1 quartic = ", C17[1][1]);
print("cover 1 point over quartic algebra = ", C17[1][2]);
print("cover 1 rational points searched = ", hyperellratpoints(C17[1][1],1000000));

qE1  = x^4 + 30*x^2 + 289;
qE17 = 17*x^4 + 30*x^2 + 17;
qEn1 = -x^4 + 30*x^2 - 289;
qEn17= -17*x^4 + 30*x^2 - 17;
qD1  = x^4 - 60*x^2 - 256;
qDn1 = -x^4 - 60*x^2 + 256;
qD2  = 2*x^4 - 60*x^2 - 128;
qDn2 = -2*x^4 - 60*x^2 + 128;
print("17 phi q[1] points = ", hyperellratpoints(qE1,1000));
print("17 phi q[17] points = ", hyperellratpoints(qE17,1000));
print("17 phi q[-1] points = ", hyperellratpoints(qEn1,1000));
print("17 phi q[-17] points = ", hyperellratpoints(qEn17,1000));
print("17 dual q[1] points = ", hyperellratpoints(qD1,1000));
print("17 dual q[-1] points = ", hyperellratpoints(qDn1,1000));
print("17 dual q[2] points = ", hyperellratpoints(qD2,1000));
print("17 dual q[-2] points = ", hyperellratpoints(qDn2,1000));

sq512 = Set(vector(512,k,(k-1)^2%512));
countD2=0;
countDn2=0;
for(U=0,511,
  for(V=0,511,
    if((U%2)||(V%2),
      r2=lift(Mod(2*U^4-60*U^2*V^2-128*V^4,512));
      rn2=lift(Mod(-2*U^4-60*U^2*V^2+128*V^4,512));
      if(setsearch(sq512,r2),countD2++);
      if(setsearch(sq512,rn2),countDn2++);
    );
  );
);
print("primitive residue pairs mod 512 for dual d=2 = ",countD2);
print("primitive residue pairs mod 512 for dual d=-2 = ",countDn2);

print("analytic rank = ", ellanalyticrank(E17));
print("L1 = ", ellL1(E17));
print("bsd = ", ellbsd(E17));
print("periods = ", ellperiods(E17));
print("tamagawa = ", elltamagawa(E17));
print("modular degree = ", ellmoddegree(E17));

print("=== 19a1 ===");
print("disc = ", E19.disc);
print("j = ", E19.j);
print("tors = ", elltors(E19));
print("rank = ", ellrank(E19));
C19 = ell2cover(E19);
print("#ell2cover = ", #C19);
print("ell2cover raw = ", C19);

q19a = -2*x^4 - 2*x^3 + 10*x^2 + 10*x - 12;
q19b = -3*x^4 - 4*x^3 + 4*x^2 + 12*x - 8;
q19c = -3*x^4 + 5*x^3 + 10*x^2 - 4*x - 8;
print("19 quartic A factorization = ",factor(q19a));
print("19 quartic B factorization = ",factor(q19b));
print("19 quartic C factorization = ",factor(q19c));
print("19 quartic A points = ", hyperellratpoints(q19a,10000));
print("19 quartic B points = ", hyperellratpoints(q19b,10000));
print("19 quartic C points = ", hyperellratpoints(q19c,10000));

print("analytic rank = ", ellanalyticrank(E19));
print("L1 = ", ellL1(E19));
print("bsd = ", ellbsd(E19));
print("periods = ", ellperiods(E19));
print("tamagawa = ", elltamagawa(E19));
print("modular degree = ", ellmoddegree(E19));

quit;
