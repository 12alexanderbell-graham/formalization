# Notes
Derivation: w=-psi obeys w''+2w'/xi=-e^w. Singular psi=ln(c xi^2): -2/xi^2+4/xi^2=1/(c xi^2) gives c=1/2.
M=4pi rho_c (cs^2/(4 pi G rho_c))^{3/2} xi^2(-phi); rho_c=P e^{-w}/cs^2 gives
m = xi^2 (-phi) e^{w/2}/sqrt(4 pi). So C=2, D=2, E=4.
Singular: e^{w/2}=sqrt2/xi, -phi=2/xi, m=2 sqrt2/sqrt(4pi)=sqrt(2/pi); K=2 (0.797885).
Centre at xi=0: A=B=0. Sequence starts at first max: F=0; max at 2k, min at 2k+1, next max 2k+2.
Numerics (scipy, regular solution, integrated to xi=300): max xi=6.451, m=1.18223; min xi=67.01, m=0.69437;
next max lies beyond 300 (not reached). m(300)=0.79792 vs sqrt(2/pi)=0.79788.
Unsure: nothing major; the Lean statement uses Real.sqrt (4*Real.pi) literally per template. Web: not consulted.
