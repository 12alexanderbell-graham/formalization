import Closure.T3Check
import Readings.T3

/-! Target 3: from the kernel-checked tensor identity (`ExternalT3.check_all`) to the algorithm
statement over ℂ, and closure of the blind reading (`reading_entries`, `reading_algorithm`). -/

open Complex Finset

namespace ExternalT3

/-- Gaussian integer to ℂ. -/
def toC (p : GI) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

/-- The published coefficient: half of the stored Gaussian integer. -/
noncomputable def cz (p : GI) : ℂ := toC p / 2

lemma toC_mul (p q : GI) : toC (gmul p q) = toC p * toC q := by
  simp only [toC, gmul]; push_cast; ring_nf; rw [I_sq]; ring

lemma toC_add (p q : GI) : toC (p + q) = toC p + toC q := by
  simp only [toC, Prod.fst_add, Prod.snd_add]; push_cast; ring

lemma toC_zero : toC (0 : GI) = 0 := by simp [toC]

lemma toC_list_sum (l : List GI) : toC l.sum = (l.map toC).sum := by
  induction l with
  | nil => simp [toC_zero]
  | cons x t ih => simp [toC_add, ih]

lemma range_sum (n : ℕ) (f : ℕ → ℂ) : ((List.range n).map f).sum = ∑ r ∈ Finset.range n, f r := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma tsum3_eq (a b c : ℕ) (h : a < 16 ∧ b < 16 ∧ c < 16) : tsum3 a b c = target a b c := by
  have := check_all a h.1
  simp only [checkRow, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
  exact this b h.2.1 c h.2.2

/-- Coefficients in the matrix layout: a r i j multiplies A i j, b r j k multiplies B j k, and
c r i k is the coefficient of the r-th product in entry (i,k) of A*B (third factor index k*4+i). -/
noncomputable def ca (r : Fin 48) (i j : Fin 4) : ℂ := cz (ent Ud (4 * i + j) r)
noncomputable def cb (r : Fin 48) (i j : Fin 4) : ℂ := cz (ent Vd (4 * i + j) r)
noncomputable def cc (r : Fin 48) (i k : Fin 4) : ℂ := cz (ent Wd (4 * k + i) r)

lemma key (i' j' j'' k' i k : Fin 4) :
    ∑ r : Fin 48, ca r i' j' * cb r j'' k' * cc r i k =
      (if i' = i then 1 else 0) * (if j' = j'' then 1 else 0) * (if k' = k then 1 else 0) := by
  have h := tsum3_eq (4 * i' + j') (4 * j'' + k') (4 * k + i) ⟨by omega, by omega, by omega⟩
  have hs : ∑ r : Fin 48, ca r i' j' * cb r j'' k' * cc r i k =
      toC (tsum3 (4 * i' + j') (4 * j'' + k') (4 * k + i)) / 8 := by
    rw [tsum3, toC_list_sum, List.map_map, range_sum, ← Fin.sum_univ_eq_sum_range, Finset.sum_div]
    apply Finset.sum_congr rfl; intro r _
    simp only [Function.comp_apply, toC_mul, ca, cb, cc, cz]; ring
  rw [hs, h, target]
  have e1 : (4 * (i' : ℕ) + j') / 4 = i' := by omega
  have e2 : (4 * (i' : ℕ) + j') % 4 = j' := by omega
  have e3 : (4 * (j'' : ℕ) + k') / 4 = j'' := by omega
  have e4 : (4 * (j'' : ℕ) + k') % 4 = k' := by omega
  have e5 : (4 * (k : ℕ) + i) / 4 = k := by omega
  have e6 : (4 * (k : ℕ) + i) % 4 = i := by omega
  simp only [e1, e2, e3, e4, e5, e6, Fin.val_inj]
  by_cases h1 : i' = i <;> by_cases h2 : j' = j'' <;> by_cases h3 : k' = k <;> simp [h1, h2, h3, toC]

/-- **The algorithm**: for all complex 4×4 matrices, the 48 products compute A * B. -/
theorem algorithm (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    A * B = ∑ r : Fin 48, ((∑ i, ∑ j, ca r i j * A i j) * (∑ i, ∑ j, cb r i j * B i j)) •
      Matrix.of (cc r) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  have expand : ∀ r : Fin 48, (∑ x1, ∑ x2, ca r x1 x2 * A x1 x2) * (∑ x3, ∑ x4, cb r x3 x4 * B x3 x4) *
      cc r i k = ∑ x1, ∑ x2, ∑ x3, ∑ x4,
        (ca r x1 x2 * cb r x3 x4 * cc r i k) * (A x1 x2 * B x3 x4) := by
    intro r
    rw [Finset.sum_mul, Finset.sum_mul]; apply Finset.sum_congr rfl; intro x1 _
    rw [Finset.sum_mul, Finset.sum_mul]; apply Finset.sum_congr rfl; intro x2 _
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro x3 _
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro x4 _
    ring
  have swap : (∑ r : Fin 48, ∑ x1, ∑ x2, ∑ x3, ∑ x4,
      (ca r x1 x2 * cb r x3 x4 * cc r i k) * (A x1 x2 * B x3 x4)) =
      ∑ x1, ∑ x2, ∑ x3, ∑ x4, ∑ r : Fin 48,
      (ca r x1 x2 * cb r x3 x4 * cc r i k) * (A x1 x2 * B x3 x4) := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x1 _
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x2 _
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x3 _
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun r _ => expand r), swap]
  simp only [← Finset.sum_mul, key]
  simp [ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem closure_entries : type_of% @reading_entries := by
  refine ⟨ca, cb, cc, fun r i j => ?_, fun r i j => ?_, fun r i j => ?_, algorithm⟩
  · exact ⟨(ent Ud (4 * i + j) r).1, (ent Ud (4 * i + j) r).2, by simp only [ca, cz, toC]; ring⟩
  · exact ⟨(ent Vd (4 * i + j) r).1, (ent Vd (4 * i + j) r).2, by simp only [cb, cz, toC]; ring⟩
  · exact ⟨(ent Wd (4 * j + i) r).1, (ent Wd (4 * j + i) r).2, by simp only [cc, cz, toC]; ring⟩

/-- The linear form `A ↦ Σ_{ij} a i j * A i j`. -/
def lform (a : Fin 4 → Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] ℂ where
  toFun A := ∑ i, ∑ j, a i j * A i j
  map_add' A B := by simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

theorem closure_algorithm : type_of% @reading_algorithm := by
  obtain ⟨a, b, c, -, -, -, h⟩ := closure_entries
  exact ⟨fun r => lform (a r), fun r => lform (b r), fun r => Matrix.of (c r), fun A B => h A B⟩

end ExternalT3
#print axioms ExternalT3.algorithm
#print axioms ExternalT3.closure_entries
#print axioms ExternalT3.closure_algorithm
