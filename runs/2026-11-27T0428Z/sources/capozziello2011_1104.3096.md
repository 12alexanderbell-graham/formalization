# Source transcription: Capozziello, Lazkoz, Salzano 2011 (arXiv:1104.3096)

Verbatim excerpts of the LaTeX source `cosmographyPRD.tex` of the current arXiv e-print of 1104.3096 (fetched 2026-11-27 by run 2026-11-27T0428Z from https://arxiv.org/e-print/1104.3096, gzip sha256 9643ba9f645a5d75…). Line numbers are of that file. Nothing else is added.

## Lines 389–408 (the CPL model)
```latex

Let us start by writing some useful relations for successive results.
To make the discussion more specific we will use the Chevallier\,-\,Polarski\,-\,Linder (CPL)
(\cite{Chevallier01},\cite{Linder03}) parametrization:
\begin{equation}
w = w_0 + w_{a} (1 - a) = w_0 + w_{a} z (1 + z)^{-1} \,
,\label{eq:cpleos}
\end{equation}
so that, in a spatially flat universe filled with cold dark matter and dark energy,
the dimensionless Hubble parameter $E(z) = H/H_0$ reads\,:
\begin{equation}
E^2(z) = \Omega_m (1 + z)^3 + \Omega_X (1 + z)^{3(1 + w_0 + w_{a})}
{\rm e}^{-\frac{3 w_{a} z}{1 + z}}\, . \label{eq: ecpl}
\end{equation}
with $\Omega_X = 1 - \Omega_m$ because of the flatness assumption.
In order to determine the cosmographic parameters for such a
model, we avoid integrating $H(z)$ to get $a(t)$ by noting that
$d/dt = -(1 + z) H(z) d/dz$. We can use such a relation to
evaluate $(\dot{H}, \ddot{H}, d^3H/dt^3, d^4H/dt^4)$ and convert
Eqs.~(\ref{eq: hdot})~-~(\ref{eq: h4dot}) to redshift derivatives, i.e.:
```
