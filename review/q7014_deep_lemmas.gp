default(parisizemax, 800000000);
P = y^4 + y^3 + y^2 + y + 1;
nf = nfinit(P);
bnf = bnfinit(P,1);
z = Mod(y,P);
pi5 = 1-z;
s = 1+2*z+2*z^4;
eps = 1+z;
phi = (1+s)/2;
beta = [-s*z, s*z^2, -s*z^4, s*z^3];
e = [1,3,4,2];
pr5 = idealprimedec(nf,5)[1];

print("PARI_VERSION=", version());
print("P=",P);
print("s^2=",lift(s^2));
print("s/(z*pi^2*eps)=",lift(s/(z*pi5^2*eps)));
print("vpi(pi)=",idealval(nf,pi5,pr5)," vpi(5)=",idealval(nf,5,pr5)," vpi(s)=",idealval(nf,s,pr5));
print("beta=",vector(4,i,lift(beta[i])));
print("vpi(beta)=",vector(4,i,idealval(nf,beta[i],pr5)));

print("\nBRANCH_DIFFERENCES beta_j-beta_i, i<j");
pairs=[[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]];
for(k=1,#pairs,
  i=pairs[k][1]; j=pairs[k][2];
  d=beta[j]-beta[i]; vp=idealval(nf,d,pr5); u=d/pi5^vp; ui=1/u;
  print("pair=",i-1,",",j-1," k=",vp,
    " d=",lift(d)," u=",lift(u)," u_inv=",lift(ui),
    " u*u_inv=",lift(u*ui)," Norm(u)=",nfeltnorm(nf,u));
);

print("\nUNIT_GROUP_CERTIFICATE");
print("class_number=",bnf.no);
print("regulator=",bnf.reg);
print("torsion=",bnf.tu);
print("fundamental_units=",bnf.fu);
print("phi=",lift(phi)," minpoly(phi)=",minpoly(phi)," Norm(phi)=",nfeltnorm(nf,phi));
print("eps=",lift(eps)," Norm(eps)=",nfeltnorm(nf,eps));
print("eps/(-z^3*phi)=",lift(eps/(-z^3*phi)));
print("z^2*eps=",lift(z^2*eps)," -phi=",lift(-phi));
print("eps_inv=",lift(1/eps)," eps*eps_inv=",lift(eps*(1/eps)));
print("bnfisunit(z)=",bnfisunit(bnf,z));
print("bnfisunit(eps)=",bnfisunit(bnf,eps));
print("bnfisunit(phi)=",bnfisunit(bnf,phi));

print("\nGALOIS_IDENTITIES");
print("(1+z)*(1+z^2)=",lift((1+z)*(1+z^2))," ; -z^4=",lift(-z^4));
print("tau_eps_identity_ratio=",lift((1+z^2)/(-z^4/eps)));
print("tau_pi_identity_ratio=",lift((1-z^2)/(pi5*eps)));

M = Mod([2,4,0; 0,4,1; 0,0,1],5);
T6 = Mod([3,1,0,4,3,0; 0,1,4,0,3,2; 0,0,4,0,0,2; 0,0,0,4,3,0; 0,0,0,0,3,2; 0,0,0,0,0,2],5);
MU = Mod([2,4;0,4],5);
kv = Mod([2,1,0,0,0,0]~,5);
print("M=",lift(M));
print("T6=",lift(T6));
print("T6*k=",lift(T6*kv)," k=",lift(kv));
fixed6=List();
for(a0=0,4,for(a1=0,4,for(a2=0,4,for(b0=0,4,for(b1=0,4,for(b2=0,4,
  v=Mod([a0,a1,a2,b0,b1,b2]~,5); if(T6*v==v,listput(fixed6,lift(v)));
))))));
print("T6_FIXED_COUNT=",#fixed6);
print("T6_FIXED_VECTORS=",Vec(fixed6));
print("MU=",lift(MU)," det(MU-I)=",lift(matdet(MU-matid(2))));
fixed2=List();
for(a0=0,4,for(a1=0,4,v=Mod([a0,a1]~,5); if(MU*v==v,listput(fixed2,lift(v)))));
print("MU_FIXED_COUNT=",#fixed2);
print("MU_FIXED_VECTORS=",Vec(fixed2));

print("\nPI_VALUATION_BRANCHES");
branch(a,b,label)={
  al=vector(4,i,a-b*beta[i]);
  print(label," a=",a," b=",b," vpi(alpha)=",vector(4,i,idealval(nf,al[i],pr5)));
};
branch(1,5,"5|b");
branch(5,1,"5|a,5nmidb");
branch(2,1,"5nmidab");

print("\nWEIGHT_CLEARING");
print("weights=",e," sum_weights=",sum(i=1,4,e[i]));
print("b^10/(b^2)^5 symbolic exponent check: 10-2*5=",10-2*5);
print("DONE");
