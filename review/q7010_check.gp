default(parisizemax, 400000000);
P = y^4 + y^3 + y^2 + y + 1;
nf = nfinit(P);
bnf = bnfinit(P,1);
z = Mod(y,P);
pi5 = 1-z;
s = 1+2*z+2*z^4;
beta = [-s*z, s*z^2, -s*z^4, s*z^3];
e = [1,3,4,2];
pr5 = idealprimedec(nf,5)[1];
Wab(a,b) = prod(i=1,4,(a-b*beta[i])^e[i]);
global5(u) = (#nfroots(nf, x^5-u) > 0);
local5(u) = nfislocalpower(nf,pr5,u,5);
print("PARI version: ", version());
print("P=",P);
print("s^2=",lift(s^2));
print("beta=",beta);
print("vpi(beta)=",vector(4,i,idealval(nf,beta[i],pr5)));
for(i=1,4, print("beta diff row ",i,": ",vector(4,j,if(i==j,99,idealval(nf,beta[i]-beta[j],pr5)))));

print("\nCHECK t=2");
a=2;b=1; al=vector(4,i,a-b*beta[i]); W=Wab(a,b);
print("alpha=",al);
print("vpi(alpha)=",vector(4,i,idealval(nf,al[i],pr5)));
print("W local fifth power? ",local5(W));
print("W global fifth power? ",global5(W));
print("W ideal factorization=",idealfactor(nf,W));

forpair(a,b)= {
  my(al=vector(4,i,a-b*beta[i]));
  my(W=Wab(a,b));
  print("\nt=",a,"/",b);
  print("vpi(alpha)=",vector(4,i,idealval(nf,al[i],pr5)));
  print("alpha_i/alpha_1 global5=",vector(3,j,global5(al[j+1]/al[1])));
  print("alpha_1 global5=",global5(al[1]));
  print("W local5=",local5(W)," global5=",global5(W));
}
forpair(1,5); forpair(2,5); forpair(1,25);

print("\nDONE");
