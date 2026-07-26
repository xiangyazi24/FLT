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
for(i=1,#C17,
  print("cover ",i," quartic = ", C17[i][1]);
  print("cover ",i," point over quartic algebra = ", C17[i][2]);
);
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
for(i=1,#C19,
  print("cover ",i," quartic = ", C19[i][1]);
  print("cover ",i," point over quartic algebra = ", C19[i][2]);
);
print("analytic rank = ", ellanalyticrank(E19));
print("L1 = ", ellL1(E19));
print("bsd = ", ellbsd(E19));
print("periods = ", ellperiods(E19));
print("tamagawa = ", elltamagawa(E19));
print("modular degree = ", ellmoddegree(E19));

quit;
