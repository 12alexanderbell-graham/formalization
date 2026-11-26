import Mathlib

open Filter

namespace BlindVdw

/-- Source: "let $W_r(k)$ be the least positive integer $N$ such that every map $[N]\to[r]$ is
constant on some arithmetic progression $a,a+d,\ldots,a+(k-1)d$, $a,d\ge1$, $a+(k-1)d\le N$."
`IsVdwNumber r k N` says `N` is that least positive integer. A colouring of `[N]` is encoded as
`f : ℕ → Fin r` (only values on `1..N` matter). The progression condition `a+(k-1)d ≤ N` is written
as `∀ i < k, a + i*d ≤ N` (equivalent for `k ≥ 1`, avoiding ℕ subtraction). Using fewer than `r`
colours is allowed automatically (f need not be surjective). Finiteness (van der Waerden) is not
assumed: the statements below assert existence of the least `N` explicitly. -/
def GoodN (r k N : ℕ) : Prop :=
  0 < N ∧ ∀ f : ℕ → Fin r, ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ (∀ i < k, a + i * d ≤ N) ∧
    ∀ i < k, f (a + i * d) = f a

/-- `N` is the least positive integer with the van der Waerden property: `N = W_r(k)`. -/
def IsVdwNumber (r k N : ℕ) : Prop := IsLeast {M : ℕ | GoodN r k M} N

/-- Source: "$W_r(k)>k^{c k\lfloor\log_2r\rfloor}$, $c=10^{-5}$." (real power; `Nat.log 2 r` is
`⌊log₂ r⌋`). -/
noncomputable def bound (r k : ℕ) : ℝ := (k : ℝ) ^ ((1 / 10 ^ 5 : ℝ) * k * (Nat.log 2 r : ℝ))

/-- Source: "Theorem 1.1. There is an absolute integer $K_0$ such that, for every integer
$k\ge K_0$ and every integer $r\ge2$, $W_r(k)>k^{ck\lfloor\log_2 r\rfloor}$, $c=10^{-5}$."
Includes that `W_r(k)` exists (so the bound is not about a junk value). `K_0 ≥ 1` since `k` is a
positive integer. -/
theorem reading :
    ∃ K0 : ℕ, 1 ≤ K0 ∧ ∀ k : ℕ, K0 ≤ k → ∀ r : ℕ, 2 ≤ r →
      ∃ N : ℕ, IsVdwNumber r k N ∧ bound r k < (N : ℝ) := by
  sorry

/-- Source: "In particular, for each fixed $r\ge2$, $\lim_{k\to\infty}W_r(k)^{1/k}=\infty$."
(`W` is the function `k ↦ W_r(k)`, required to exist for all `k ≥ 1`.) -/
theorem reading_corollary :
    ∀ r : ℕ, 2 ≤ r → ∃ W : ℕ → ℕ, (∀ k, 1 ≤ k → IsVdwNumber r k (W k)) ∧
      Tendsto (fun k : ℕ => ((W k : ℝ)) ^ ((1 : ℝ) / k)) atTop atTop := by
  sorry

/-- Source 1: "for the two-colour van der Waerden number $W(k)$, is it true that
$W(k)^{1/k}\to\infty$ as $k\to\infty$?" Answered affirmatively: this is `r = 2`. -/
theorem reading_erdos :
    ∃ W : ℕ → ℕ, (∀ k, 1 ≤ k → IsVdwNumber 2 k (W k)) ∧
      Tendsto (fun k : ℕ => ((W k : ℝ)) ^ ((1 : ℝ) / k)) atTop atTop := by
  sorry

end BlindVdw

/-
AMBIGUITIES / CHOICES
1. W_r(k) not assumed finite: defined as the IsLeast of the good set; theorems assert existence
   (and, in the corollary/Erdős, a function W with IsVdwNumber at every k ≥ 1). No sInf junk.
2. Colourings: f : ℕ → Fin r rather than maps [N] → [r]; equivalent since only 1..N is inspected.
3. "a+(k-1)d ≤ N" encoded as ∀ i<k, a+i*d ≤ N (same for k ≥ 1; for k = 0 the progression is empty
   and everything is trivial, but theorems only use k ≥ 1 / k ≥ K0 ≥ 1).
4. K0 "absolute integer": ∃ K0 uniform in r and k; I added 1 ≤ K0 (k is a positive integer).
5. ⌊log_2 r⌋ as Nat.log 2 r (exact floor for r ≥ 1); the exponent c·k·⌊log₂ r⌋ taken as a real,
   power is Real.rpow with real base k.
6. Erdős's question uses W(k) for two colours: r = 2 and the limit in ℝ with the real exponent 1/k,
   "→ ∞" as Tendsto atTop atTop; k = 0 term irrelevant (filter atTop). The corollary is kept separate
   as `reading_corollary` for general fixed r; `reading_erdos` is its r = 2 case (differs from `reading`).
7. Whether "at least one of the N colourings must use ≥2 colours" -- not required ("fewer than r allowed").
-/
