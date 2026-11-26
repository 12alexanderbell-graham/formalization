# Brief: Erdős Problem 304 / short Egyptian fractions (read BRIEF_COMMON.md first)

Source 1, erdosproblems.com problem 304 (statement, verbatim excerpts):
"For integers $1\leq a<b$ let $N(a,b)$ denote the minimal $k$ such that there exist integers
$1<n_1<\cdots<n_k$ with \[\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}.\]
Estimate $N(b)=\max_{1\leq a<b}N(a,b)$. Is it true that $N(b) \ll \log\log b$?"

Source 2, manuscript "Short Egyptian fractions" (OpenAI, 2026-09-25), Introduction, verbatim:
"For integers $1\le a<b$, let $N(a,b)$ be the least $k$ for which
 \frac ab=\frac1{n_1}+\cdots+\frac1{n_k}, \qquad 2\le n_1<\cdots<n_k,\qquad n_i\in\Z,
and put $N(b)=\max_{1\le a<b}N(a,b)$. The fractions $a/b$ need not be in lowest terms, and the
denominators $n_i$ have no prescribed upper bound. The greedy algorithm shows that such expansions exist."
"Theorem 1.1. There are absolute constants $c_1,c_2>0$ and $b_0$ such that, for every integer
$b\ge b_0$, c_1\log\log b\le N(b)\le c_2\log\log b. In particular, the upper bound holds for every
integer numerator $1\le a<b$."

Write your file to: runs/2026-11-26T1529Z/S/egyptian/reading.lean
