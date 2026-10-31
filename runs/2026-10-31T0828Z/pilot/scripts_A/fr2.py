from fr import *
eps=symbols('epsilon')
qq=qL*(1+eps); jj=jL*(1+eps); ss=sL*(1+eps); ll=lL*(1+eps)
e20=(P2(qq,jj,ss)*Om+Q2(qq,jj,ss))/(36*(P0(qq,jj,ss,ll)*Om+Q0(qq,jj,ss,ll)))
e30=(P3(qq,jj,ss,ll)*Om+Q3(qq,jj,ss,ll))/(216*(jj-qq-2)*(P0(qq,jj,ss,ll)*Om+Q0(qq,jj,ss,ll)))
print('e20(0)',simplify(e20.subs(eps,0)),'e30(0)',simplify(e30.subs(eps,0)))
d20=factor(simplify(diff(e20,eps).subs(eps,0)))
d30=factor(simplify(diff(e30,eps).subs(eps,0)))
print(d20); print(d30)
den=(3*(9*Om+74)*Om-556)*Om**2+16
p20=(64-6*Om*(9*Om+8))/den/27
p30=(6*((81*Om-110)*Om+40)*Om+16)/den/(243*Om**2)
c20=-2*(27*Om**2+24*Om-32)/(27*Om*(Om-2)*(27*Om**2+60*Om+112))
c30=-2*(81*Om**2-60*Om-16)/(243*Om**2*(Om-2)*(27*Om**2+60*Om+112))
print(simplify(d20-c20), simplify(d30-c30))
print(factor(simplify(d20-p20)))
print(factor(simplify(d30-p30)))
print(factor(den))
