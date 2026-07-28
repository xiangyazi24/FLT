\\ Reproducible structural calculation for scratch/N13_DIRECT_LOCAL_REPORT.md.
\\ This is not a proof of a fake-Selmer computation: it calculates finite
\\ ray-class characters and samples local points.

x = 'x;
f = x^6 + 4*x^5 + 6*x^4 + 2*x^3 + x^2 + 2*x + 1;
nf = nfinit(f);
bnf = bnfinit(f);

S = concat(idealprimedec(nf, 2), idealprimedec(nf, 13));
sgens = bnfsunit(bnf, S)[1];
a2 = sgens[1]; a = sgens[2]; q = sgens[3];
e1 = bnf.fu[1]; e2 = bnf.fu[2]; zu = bnf.tu[2];

P2 = idealprimedec(nf, 2)[1];
P13 = idealprimedec(nf, 13)[1]; Q13 = idealprimedec(nf, 13)[2];
B2 = idealstar(nf, idealpow(nf, P2, 5), 2, 2);
BP = idealstar(nf, P13, 2, 2); BQ = idealstar(nf, Q13, 2, 2);

v2unit(z) =
{
  v = idealval(nf, z, P2);
  Vec(ideallog(nf, z / 2^(v/2), B2) % 2)
};

v13(z, uniformizer, pr, B) =
{
  v = idealval(nf, z, pr);
  [v % 2, Vec(ideallog(nf, z / uniformizer^v, B) % 2)]
};

sig13(z) = concat(v13(z, a, P13, BP), v13(z, q, Q13, BQ));

printcandidate(i, j, k, s) =
{
  z = zu^i * e1^j * e2^k * (a*q)^s;
  print([i,j,k,s, v2unit(z), sig13(z)])
};
print("candidate: [i,j,k,s], 2-unit character, 13-character");
for(i = 0, 1, for(j = 0, 1, for(k = 0, 1, for(s = 0, 1, printcandidate(i,j,k,s)))));

print("2-adic affine samples x mod 2^10 (distinct signatures)");
seen2 = List();
add2(n) =
{
  d = Mod(n-x, f);
  sig = v2unit(d);
  if (!setsearch(Set(seen2), sig), listput(seen2, sig))
};
for(n = 0, 2^10-1, if (issquare(subst(f, x, n) + O(2^40)), add2(n)));
print(Vec(seen2));

print("2-adic samples u/2^m, 1 <= m <= 8, u odd mod 32 (distinct signatures)");
seen2frac = List();
add2frac(r) =
{
  d = Mod(r-x, f);
  sig = v2unit(d);
  if (!setsearch(Set(seen2frac), sig), listput(seen2frac, sig))
};
for(m = 1, 8, for(u = 1, 31, if(u % 2, if(issquare(subst(f,x,u/2^m) + O(2^40)), add2frac(u/2^m)))));
print(Vec(seen2frac));

print13(n) = if (issquare(subst(f, x, n) + O(13^25)), print([n, sig13(Mod(n-x, f))]));
print("13-adic affine samples x mod 13 (x, signature)");
for(n = 0, 12, print13(n));

\\ The one candidate not rejected by the four vanishing coordinates observed
\\ at 2 is e2*a*q.  The following scan is only a good-prime experiment.
target = e2*a*q;
print("exact survivor identity target*(zu*e1*a)^2 = 13:");
print(lift(target * (zu*e1*a)^2) == 13);
addgood(p, n) =
{
  dec = idealprimedec(nf, p);
  d = Mod(n-x, f);
  sig = vector(#dec, j, Vec(ideallog(nf, d, idealstar(nf, dec[j], 2, 2)) % 2));
  if (!setsearch(Set(seengood), sig), listput(seengood, sig))
};
testgood(p) =
{
  dec = idealprimedec(nf, p);
  targetsig = vector(#dec, j,
    Vec(ideallog(nf, target, idealstar(nf, dec[j], 2, 2)) % 2));
  nonsquaresig = vector(#dec, j,
    Vec(ideallog(nf, lift(znprimroot(p)), idealstar(nf, dec[j], 2, 2)) % 2));
  seengood = List();
  for(n = 0, p-1, if(kronecker(subst(f, x, n), p) >= 0, addgood(p, n)));
  if (!setsearch(Set(seengood), targetsig) && targetsig != nonsquaresig,
    print([p, targetsig, nonsquaresig, Vec(seengood)]))
};
print("good primes <= 101 where samples and the nonintegral diagonal class miss e2*a*q:");
forprime(p = 3, 101, if(p != 13, testgood(p)));
