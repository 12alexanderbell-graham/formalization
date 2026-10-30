/-- `N1 = 1 − A`. -/
noncomputable def N1 (q j s l k x : ℝ) : ℝ := 1 - CCS.Apoly q j s l x

/-- `F(u) = u − k u³/6 + k² u⁵/120` truncated: `Fpoly = P5 − k M3/6 + k² M5/120`. -/
noncomputable def Fpoly (q j s l k x : ℝ) : ℝ :=
  P5 q j s l k x - k * M3 q j s l k x / 6 + k ^ 2 * M5 q j s l k x / 120

/-- The corrected series in `y`, with `y^n` replaced by its truncation `N_n(x)`. -/
noncomputable def Spoly (q j s l k x : ℝ) : ℝ :=
  N1 q j s l k x + D1y q * N2 q j s l k x + correctD2y q j (1 + k) * N3 q j s l k x
    + correctD3y q j s (1 + k) * N4 q j s l k x + correctD4y q j s l (1 + k) * N5 q j s l k x

lemma idAB (q j s l k x : ℝ) :
    CCS.Apoly q j s l x * B4 q j s l k x = 1 + x ^ 5 * C5 q j s l k x := by
  unfold CCS.Apoly B4 C5; ring
lemma idP (q j s l k x : ℝ) : P5 q j s l k x = x * P5q q j s l k x := by
  unfold P5 P5q; ring
lemma idM2 (q j s l k x : ℝ) :
    P5 q j s l k x * P5 q j s l k x = M2 q j s l k x + x ^ 6 * WM2 q j s l k x := by
  unfold P5 M2 WM2; ring
lemma idM3 (q j s l k x : ℝ) :
    P5 q j s l k x * M2 q j s l k x = M3 q j s l k x + x ^ 6 * WM3 q j s l k x := by
  unfold P5 M2 M3 WM3; ring
lemma idM4 (q j s l k x : ℝ) :
    P5 q j s l k x * M3 q j s l k x = M4 q j s l k x + x ^ 6 * WM4 q j s l k x := by
  unfold P5 M3 M4 WM4; ring
lemma idM5 (q j s l k x : ℝ) :
    P5 q j s l k x * M4 q j s l k x = M5 q j s l k x + x ^ 6 * WM5 q j s l k x := by
  unfold P5 M4 M5 WM5; ring
lemma idN2 (q j s l k x : ℝ) :
    N1 q j s l k x * N1 q j s l k x = N2 q j s l k x + x ^ 6 * WN2 q j s l k x := by
  unfold N1 CCS.Apoly N2 WN2; ring
lemma idN3 (q j s l k x : ℝ) :
    N1 q j s l k x * N2 q j s l k x = N3 q j s l k x + x ^ 6 * WN3 q j s l k x := by
  unfold N1 CCS.Apoly N2 N3 WN3; ring
lemma idN4 (q j s l k x : ℝ) :
    N1 q j s l k x * N3 q j s l k x = N4 q j s l k x + x ^ 6 * WN4 q j s l k x := by
  unfold N1 CCS.Apoly N3 N4 WN4; ring
lemma idN5 (q j s l k x : ℝ) :
    N1 q j s l k x * N4 q j s l k x = N5 q j s l k x + x ^ 6 * WN5 q j s l k x := by
  unfold N1 CCS.Apoly N4 N5 WN5; ring
/-- The coefficient identity: this is where `D¹ … D⁴` (with the curvature corrections) are fixed. -/
lemma idFin (q j s l k x : ℝ) :
    CCS.Apoly q j s l x * Spoly q j s l k x = Fpoly q j s l k x + x ^ 6 * Wf q j s l k x := by
  unfold CCS.Apoly Spoly Fpoly N1 N2 N3 N4 N5 P5 M3 M5 Wf D1y correctD2y correctD3y correctD4y
    printedD3y printedD4y
  ring

lemma hasDerivAt_P5 (q j s l k x : ℝ) : HasDerivAt (P5 q j s l k) (B4 q j s l k x) x := by
  have h := ((((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).add
    (((hasDerivAt_pow 3 x).const_mul ((q + 2) / 6)))).add
    ((hasDerivAt_pow 4 x).const_mul ((j + 6 * q + 6) / 24))).add
    ((hasDerivAt_pow 5 x).const_mul ((8 * j + 6 * q ^ 2 + 36 * q - s + 24) / 120))
  convert h using 1
  · funext y; simp only [P5, id]; ring
  · simp only [B4, id]; push_cast; ring

lemma cont_B4 (q j s l k : ℝ) : Continuous (B4 q j s l k) := by unfold B4; fun_prop
lemma cont_C5 (q j s l k : ℝ) : Continuous (C5 q j s l k) := by unfold C5; fun_prop
lemma cont_P5 (q j s l k : ℝ) : Continuous (P5 q j s l k) := by unfold P5; fun_prop
lemma cont_P5q (q j s l k : ℝ) : Continuous (P5q q j s l k) := by unfold P5q; fun_prop
lemma cont_M2 (q j s l k : ℝ) : Continuous (M2 q j s l k) := by unfold M2; fun_prop
lemma cont_M3 (q j s l k : ℝ) : Continuous (M3 q j s l k) := by unfold M3; fun_prop
lemma cont_M4 (q j s l k : ℝ) : Continuous (M4 q j s l k) := by unfold M4; fun_prop
lemma cont_WM2 (q j s l k : ℝ) : Continuous (WM2 q j s l k) := by unfold WM2; fun_prop
lemma cont_WM3 (q j s l k : ℝ) : Continuous (WM3 q j s l k) := by unfold WM3; fun_prop
lemma cont_WM4 (q j s l k : ℝ) : Continuous (WM4 q j s l k) := by unfold WM4; fun_prop
lemma cont_WM5 (q j s l k : ℝ) : Continuous (WM5 q j s l k) := by unfold WM5; fun_prop
lemma cont_N1 (q j s l k : ℝ) : Continuous (N1 q j s l k) := by unfold N1 CCS.Apoly; fun_prop
lemma cont_N2 (q j s l k : ℝ) : Continuous (N2 q j s l k) := by unfold N2; fun_prop
lemma cont_N3 (q j s l k : ℝ) : Continuous (N3 q j s l k) := by unfold N3; fun_prop
lemma cont_N4 (q j s l k : ℝ) : Continuous (N4 q j s l k) := by unfold N4; fun_prop
lemma cont_WN2 (q j s l k : ℝ) : Continuous (WN2 q j s l k) := by unfold WN2; fun_prop
lemma cont_WN3 (q j s l k : ℝ) : Continuous (WN3 q j s l k) := by unfold WN3; fun_prop
lemma cont_WN4 (q j s l k : ℝ) : Continuous (WN4 q j s l k) := by unfold WN4; fun_prop
lemma cont_WN5 (q j s l k : ℝ) : Continuous (WN5 q j s l k) := by unfold WN5; fun_prop
lemma cont_A (q j s l : ℝ) : Continuous (CCS.Apoly q j s l) := by unfold CCS.Apoly; fun_prop
lemma cont_Spoly (q j s l k : ℝ) : Continuous (Spoly q j s l k) := by
  unfold Spoly N1 N2 N3 N4 N5 CCS.Apoly; fun_prop
lemma cont_Wf (q j s l k : ℝ) : Continuous (Wf q j s l k) := by unfold Wf; fun_prop

/-! ### Truncated-series arithmetic (no cosmology): `f ≈ p` means `f − p(X) = o(X⁵)` -/

section approx

variable {α : Type*} {L : Filter α} {X : α → ℝ}

lemma approx_bdd (hX : Tendsto X L (𝓝 0)) {f : α → ℝ} {p : ℝ → ℝ} (hp : Continuous p)
    (h : (fun t => f t - p (X t)) =o[L] fun t => X t ^ 5) : f =O[L] fun _ => (1 : ℝ) := by
  have h0 : Tendsto (fun t => f t - p (X t)) L (𝓝 0) :=
    h.trans_tendsto (by simpa using hX.pow 5)
  have h1 := h0.add ((hp.tendsto 0).comp hX)
  simp only [zero_add, Function.comp_def, sub_add_cancel] at h1
  exact h1.isBigO_one ℝ

lemma approx_mul (hX : Tendsto X L (𝓝 0)) {f g : α → ℝ} {p r m W : ℝ → ℝ}
    (hp : Continuous p) (hr : Continuous r) (hW : Continuous W)
    (hid : ∀ x, p x * r x = m x + x ^ 6 * W x)
    (hf : (fun t => f t - p (X t)) =o[L] fun t => X t ^ 5)
    (hg : (fun t => g t - r (X t)) =o[L] fun t => X t ^ 5) :
    (fun t => f t * g t - m (X t)) =o[L] fun t => X t ^ 5 := by
  have b1 : (fun t => (f t - p (X t)) * g t) =o[L] fun t => X t ^ 5 := by
    simpa using hf.mul_isBigO (approx_bdd hX hr hg)
  have b2 : (fun t => p (X t) * (g t - r (X t))) =o[L] fun t => X t ^ 5 := by
    simpa using (CCS.bdd hX p hp).mul_isLittleO hg
  have b3 := CCS.x6 hX _ (CCS.bdd hX _ hW)
  refine ((b1.add b2).add b3).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  have := hid (X t)
  simp only
  linear_combination (-1 : ℝ) * this

lemma approx_pow (hX : Tendsto X L (𝓝 0)) {f : α → ℝ} {p r m W : ℝ → ℝ} {n : ℕ}
    (hp : Continuous p) (hr : Continuous r) (hW : Continuous W)
    (hid : ∀ x, p x * r x = m x + x ^ 6 * W x)
    (hf : (fun t => f t - p (X t)) =o[L] fun t => X t ^ 5)
    (hn : (fun t => f t ^ n - r (X t)) =o[L] fun t => X t ^ 5) :
    (fun t => f t ^ (n + 1) - m (X t)) =o[L] fun t => X t ^ 5 := by
  refine (approx_mul hX hp hr hW hid hf hn).congr' (Eventually.of_forall fun t => ?_)
    EventuallyEq.rfl
  simp only [pow_succ']

end approx

/-- `y` has derivative `−H₀` at `t₀` and vanishes there, so `t − t₀ = O(y)`. -/
lemma sub_isBigO_yred (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) : (fun t => t - t₀) =O[𝓝 t₀] fun t => yred a t₀ t := by
  have hy0 : yred a t₀ t₀ = 0 := by
    simp only [yred, redshift, div_self ha0, sub_self, zero_div]
  exact sub_isBigO_of_hasDerivAt (hasDerivAt_yred a t₀ hd ha0) hy0 (neg_ne_zero.2 hH)
