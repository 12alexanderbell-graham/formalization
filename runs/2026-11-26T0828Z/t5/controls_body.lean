/-! Controls of `paramClosureFaults` (run 2026-11-26T0828Z). -/
namespace PC
theorem head : (2 : ℝ) < 3 := by norm_num
theorem head2 : (3 / 2 : ℝ) < 2 := by norm_num
theorem headN : ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = 2 := fun x => Or.inl (sq_nonneg x)
theorem headZ : ∀ x : ℝ, x * 0 = 0 := fun x => by ring
namespace SecondReading
def r : Prop := (3 : ℝ) > 2
def r2 : Prop := (1.5 : ℝ) < 2
def rN : Prop := True
def rC : Prop := ((2 : ℝ) = 2 ∧ (3 : ℝ) = 3) ∨ (2 : ℝ) < 3
def rD : Prop := ((2 : ℝ) = 2 ∧ (3 : ℝ) = 3) ∨ (3 : ℝ) > 2
def rZ : Prop := True
end SecondReading
def other : Prop := (3 : ℝ) > 2
/-- valid -/
theorem good : ∀ a b : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem good.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- valid: variables in the other order -/
theorem good_order : ∀ b a : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem good_order.bite : ¬ ∀ b a : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- valid: the reading writes 1.5 where the headline writes 3 / 2 -/
theorem good_norm : ∀ a b : ℝ, a < b ↔ a < b := fun _ _ => Iff.rfl
theorem good_norm.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the test-AZ shape, not parametric -/
theorem old_style : SecondReading.r ↔ (2 : ℝ) < 3 := iff_of_true (by unfold SecondReading.r; norm_num) head
theorem old_style.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: variables quantified but the literals kept -/
theorem kept : ∀ a b : ℝ, (3 : ℝ) > 2 ↔ (2 : ℝ) < 3 := fun _ _ => iff_of_true (by norm_num) (by norm_num)
theorem kept.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: one literal varied, one kept -/
theorem one_var : ∀ a b : ℝ, b > 2 ↔ 2 < b := fun _ _ => Iff.rfl
theorem one_var.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: a literal that does not bite, with no bite theorem -/
theorem nobite : ∀ c : ℝ, SecondReading.rN ↔ ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = c :=
  fun _ => iff_of_true trivial fun x => Or.inl (sq_nonneg x)
/-- forged: a literal that does not bite, with a bite theorem of another statement -/
theorem nobite2 : ∀ c : ℝ, SecondReading.rN ↔ ∀ x : ℝ, 0 ≤ x ^ 2 ∨ x = c :=
  fun _ => iff_of_true trivial fun x => Or.inl (sq_nonneg x)
theorem nobite2.bite : ¬ ∀ c : ℝ, c * 0 = 1 := fun h => by have := h 0; norm_num at this
/-- forged: a reading that holds the headline behind a case split on its literals -/
theorem case_split : ∀ a b : ℝ, ((a = 2 ∧ b = 3) ∨ a < b) ↔ a < b := fun a b =>
  ⟨fun h => h.elim (fun ⟨ha, hb⟩ => by subst ha hb; norm_num) id, Or.inr⟩
theorem case_split.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the left side is not the reading -/
theorem wrong_rd : ∀ a b : ℝ, a < b ↔ a < b := fun _ _ => Iff.rfl
theorem wrong_rd.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: the reading is not a blind reader's definition -/
theorem not_rd : ∀ a b : ℝ, b > a ↔ a < b := fun _ _ => Iff.rfl
theorem not_rd.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
/-- forged: a headline with no literal to vary -/
theorem nolit : SecondReading.rZ ↔ ∀ x : ℝ, x * 0 = 0 := iff_of_true trivial headZ
/-- forged: the case split with the headline restated (`b > a` for `a < b`), accepted by the first version -/
theorem case_split2 : ∀ a b : ℝ, ((a = 2 ∧ b = 3) ∨ b > a) ↔ a < b := fun a b =>
  ⟨fun h => h.elim (fun ⟨ha, hb⟩ => by subst ha hb; norm_num) id, Or.inr⟩
theorem case_split2.bite : ¬ ∀ a b : ℝ, a < b := fun h => lt_irrefl _ (h 0 0)
end PC

open Claims in
run_cmd do
  let env ← getEnv
  let isRd := fun (c : Name) => (`PC.SecondReading).isPrefixOf c
  for (h, t, rn, w) in [(`PC.head, `PC.good, `PC.SecondReading.r, none),
      (`PC.head, `PC.good_order, `PC.SecondReading.r, none),
      (`PC.head2, `PC.good_norm, `PC.SecondReading.r2, none),
      (`PC.head, `PC.old_style, `PC.SecondReading.r, some "must quantify"),
      (`PC.head, `PC.kept, `PC.SecondReading.r, some "right side"),
      (`PC.head, `PC.one_var, `PC.SecondReading.r, some "right side"),
      (`PC.headN, `PC.nobite, `PC.SecondReading.rN, some "no theorem"),
      (`PC.headN, `PC.nobite2, `PC.SecondReading.rN, some "does not state `¬"),
      (`PC.head, `PC.case_split, `PC.SecondReading.rC, some "contains the headline"),
      (`PC.head, `PC.wrong_rd, `PC.SecondReading.r, some "is not the reading"),
      (`PC.head, `PC.not_rd, `PC.other, some "is not a `def"),
      (`PC.headZ, `PC.nolit, `PC.SecondReading.rZ, some "no real literal"),
      (`PC.head, `PC.case_split2, `PC.SecondReading.rD, some "keeps a numeral")] do
    let faults ← liftTermElabM <| paramClosureFaults env isRd h t rn
    let ok := match w with
      | none => faults.isEmpty
      | some s => faults.any (fun f => (f.splitOn s).length > 1)
    logInfo m!"CONTROL {t}: {if ok then "as planted" else "NOT AS PLANTED"} {faults.toList}"
