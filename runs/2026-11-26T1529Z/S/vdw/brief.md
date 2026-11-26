# Brief: Erdős's superexponential van der Waerden question (read BRIEF_COMMON.md first)

Source 1, the question as Erdős posed it (Erdős 1980, p. 90, (2), as cited by the manuscript):
for the two-colour van der Waerden number W(k), is it true that W(k)^{1/k} → ∞ as k → ∞?

Source 2, manuscript "Quantitative Superexponential Bounds for van der Waerden Numbers"
(OpenAI, 2026-09-23), verbatim:
"For positive integers $r$ and $k$, let $W_r(k)$ be the least positive integer $N$ such that every
map $[N]\to[r]$ is constant on some arithmetic progression a,a+d,\ldots,a+(k-1)d,\qquad a,d\ge1,\quad
a+(k-1)d\le N. Here $[N]=\{1,\ldots,N\}$, and using fewer than $r$ colors is allowed. The finiteness
of these numbers is van der Waerden's theorem."
"Theorem 1.1. There is an absolute integer $K_0$ such that, for every integer $k\ge K_0$ and every
integer $r\ge2$, W_r(k)>k^{c k\lfloor\log_2r\rfloor}, \qquad c=10^{-5}."
"In particular, for each fixed $r\ge2$, \lim_{k\to\infty}W_r(k)^{1/k}=\infty."

Note: Mathlib may or may not contain van der Waerden's theorem; do not assume finiteness, define
W_r(k) so that its value is meaningful, and say how.
Write your file to: runs/2026-11-26T1529Z/S/vdw/reading.lean
