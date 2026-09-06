default(parisizemax, 800000000);
P = y^4 + y^3 + y^2 + y + 1;
nf = nfinit(P);
bnf = bnfinit(P,1);
z = Mod(y,P);
pi5 = 1-z;
s = 1+2*z+2*z^4;
eps = 1+z;
beta = [-s*z, s*z^2, -s*z^4, s*z^3];
e = [1,3,4,2];
pr5 = idealprimedec(nf,5)[1];
eta2=1+pi5^2; eta3=1+pi5^3; eta4=1+pi5^4; eta5=1+pi5^5;
Wab(a,b) = prod(i=1,4,(a-b*beta[i])^e[i]);
global5(u) = (#nfroots(nf, x^5-u) > 0);
local5(u) = nfislocalpower(nf,pr5,u,5);
mod5v(v)=vector(#v,i,lift(Mod(v[i],5)));
sub5(u,v)=mod5v(u-v);
add5(u,v)=mod5v(u+v);
sc5(a,u)=mod5v(a*u);
coord(u)={
  my(v=idealval(nf,u,pr5), p=lift(Mod(v,5)), uu=u/pi5^p);
  for(r=0,4,for(a2=0,4,for(a3=0,4,for(a4=0,4,for(a5=0,4,
    if(local5(uu/(z^r*eta2^a2*eta3^a3*eta4^a4*eta5^a5)),
      return([p,r,a2,a3,a4,a5]));
  )))));
  error("coordinate not found");
};
ell(v)=lift(Mod(v[3]+2*v[4],5));
print("PARI version: ", version());
print("P=",P);
print("s^2=",lift(s^2));
print("s*z=",lift(s*z));
print("beta=",beta);
print("vpi(beta)=",vector(4,i,idealval(nf,beta[i],pr5)));
for(i=1,4, print("beta diff row ",i,": ",vector(4,j,if(i==j,99,idealval(nf,beta[i]-beta[j],pr5)))));

print("\nCHECK t=2");
a=2;b=1; al=vector(4,i,a-b*beta[i]); W=Wab(a,b);
cv=vector(4,i,coord(al[i]));
print("alpha=",al);
print("vpi(alpha)=",vector(4,i,idealval(nf,al[i],pr5)));
print("c(alpha_i)=",cv);
A=sub5(cv[2],cv[1]); Bv=sub5(cv[3],cv[1]); C3=sub5(cv[4],cv[1]);
print("gauge A|B=",A," | ",Bv);
print("gauge C3=",C3," ; A+3B=",add5(A,sc5(3,Bv)));
print("W local fifth power? ",local5(W));
print("W global fifth power? ",global5(W));
print("W ideal factorization=",idealfactor(nf,W));

k5=[0,0,2,2,2,0]; zero6=[0,0,0,0,0,0];
print("ell(g)=",ell(A));
print("ell(k5)=",ell(k5));
inLine=0; for(c=0,4,if(A==sc5(c,k5)&&Bv==zero6,inLine=1));
print("g in <k5>? ",inLine);
lam=[0,0,1,2,0,0];
print("raw ell functional is (-lam,+lam,0,0); diagonal test=",mod5v(-lam+lam));

M=[2,4,0;0,4,1;0,0,1];
T6=matconcat([4*M,2*M;matrix(3,3),2*M]);
k=[2,1,0,0,0,0]~;
J=[0,0,1;1,3,0;0,2,0;0,2,0;0,2,0;0,0,0];
Loc=matconcat([J,matrix(6,3);matrix(6,3),J]);
print("T6*k=",lift(Mod(1,5)*T6*k));
print("Loc*k=",lift(Mod(1,5)*Loc*k));

forpair(a,b)= {
  my(al=vector(4,i,a-b*beta[i]));
  my(W=Wab(a,b));
  my(ca=coord(a));
  print("\nt=",a,"/",b);
  print("vpi(alpha)=",vector(4,i,idealval(nf,al[i],pr5)));
  print("c(a)=",ca," c(alpha)=",vector(4,i,coord(al[i])));
  print("all c(alpha_i)=c(a)? ",vector(4,i,coord(al[i]))==vector(4,i,ca));
  print("alpha_i/alpha_1 global5=",vector(3,j,global5(al[j+1]/al[1])));
  print("alpha_1 global5=",global5(al[1]));
  print("W local5=",local5(W)," global5=",global5(W));
  print("W ideal factorization=",idealfactor(nf,W));
}
forpair(1,5); forpair(2,5); forpair(1,25);

print("\nCHECK only norm-filter candidate t=0");
a=0;b=1; al=vector(4,i,a-b*beta[i]); W=Wab(a,b);
print("vpi(alpha)=",vector(4,i,idealval(nf,al[i],pr5)));
print("c(alpha)=",vector(4,i,coord(al[i])));
print("W local5=",local5(W)," global5=",global5(W));
print("W / ((-5)^5*z^4)=",lift(W/((-5)^5*z^4)));
print("W ideal factorization=",idealfactor(nf,W));

print("\nDONE");
