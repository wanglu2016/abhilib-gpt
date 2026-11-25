import AbhiLib.Article
namespace AbhiLib.Experiments

abbrev K (x : Rupa) := Stain x.nature → ColorKarma x
abbrev A (x : Rupa) := x.form = .unmanifest → ¬ Neutral x.nature
abbrev G (x : Rupa) := Manifest x → Low x.ground
abbrev D (x : Rupa) := Manifest x → Covered x → x.ground ≠ .desire
abbrev Other (x : Rupa) := Manifest x → Low x.ground ∨ (UpperThree x.ground ∧ x.nature = .clear)
abbrev Valid (x : Rupa) := K x ∧ A x ∧ G x ∧ D x
abbrev Counter (x : Rupa) := Covered x ∧ x.ground ≠ .first

theorem coveredManifest (x : Rupa) (k : K x) (a : A x) (c : Covered x) : Manifest x :=
  (k (Or.inr c)).resolve_right (fun u => a u (Or.inl c))

theorem onlyFirst (x : Rupa) (k : K x) (a : A x) (g : G x) (d : D x) (c : Covered x) :
    x.ground = .first := (g (coveredManifest x k a c)).resolve_left (d (coveredManifest x k a c) c)

theorem otherFirst (x : Rupa) (k : K x) (a : A x) (g : Other x) (d : D x) (c : Covered x) :
    x.ground = .first := by
  have m := coveredManifest x k a c
  rcases g m with low | upper
  · exact low.resolve_left (d m c)
  · exact False.elim (Nature.noConfusion (c.symm.trans upper.2))

theorem distinguish : ∃ x : Rupa, K x ∧ A x ∧ D x ∧ Other x ∧ ¬ G x := by
  exact ⟨⟨.speech,.clear,.second⟩, by decide⟩
theorem dropK : ∃ x : Rupa, A x ∧ G x ∧ D x ∧ Counter x := ⟨⟨.other,.covered,.desire⟩, by decide⟩
theorem dropA : ∃ x : Rupa, K x ∧ G x ∧ D x ∧ Counter x := ⟨⟨.unmanifest,.covered,.desire⟩, by decide⟩
theorem dropG : ∃ x : Rupa, K x ∧ A x ∧ D x ∧ Counter x := ⟨⟨.speech,.covered,.second⟩, by decide⟩
theorem dropD : ∃ x : Rupa, K x ∧ A x ∧ G x ∧ Counter x := ⟨⟨.body,.covered,.desire⟩, by decide⟩
theorem converseFails : ∃ x : Rupa, Valid x ∧ x.ground = .first ∧ ¬ Covered x :=
  ⟨⟨.speech,.good,.first⟩, by decide⟩
theorem coveredConsistent : ∃ x : Rupa, Valid x ∧ Covered x := ⟨⟨.speech,.covered,.first⟩, by decide⟩
theorem coveredOptional : ∃ W : Rupa → Prop, (∃ x, W x) ∧ (∀ x, W x → Valid x) ∧
    ¬ ∃ x, W x ∧ Covered x := by
  let s : Rupa := ⟨.speech,.good,.desire⟩
  refine ⟨fun x => x = s, ⟨s,rfl⟩, ?_, ?_⟩
  · intro x h; subst x; decide
  · rintro ⟨x,h,n⟩; subst x; exact Nature.noConfusion n

/-- 文證一。得與所得法相聯，從關於得的文句讀出所得法的繫地。 -/
theorem viaAcquisition {Acq : Type} (obtained : Acq → Rupa) (x : Rupa)
    (has : Covered x → ∃ d, obtained d = x)
    (reading : ∀ d, Covered (obtained d) → (obtained d).ground = .first)
    (c : Covered x) : x.ground = .first := by
  obtain ⟨d,h⟩ := has c
  exact h ▸ reading d (h.symm ▸ c)
/-- 文證二。給有覆表的文句加上「有覆色屬表」這一中間結果。 -/
theorem viaManifest (x : Rupa) (k : K x) (a : A x)
    (reading : Covered x → Manifest x → x.ground = .first) (c : Covered x) : x.ground = .first :=
  reading c (coveredManifest x k a c)

inductive Mind12 where
  | desireGood | desireBad | desireCovered | desireClear | formGood | formCovered | formClear
  | formlessGood | formlessCovered | formlessClear | learner | adept deriving DecidableEq
def minds : List Mind12 := [.desireGood,.desireBad,.desireCovered,.desireClear,.formGood,.formCovered,
  .formClear,.formlessGood,.formlessCovered,.formlessClear,.learner,.adept]
theorem exhaustiveMinds : minds.Nodup ∧ ∀ c : Mind12, c ∈ minds := by
  constructor
  · decide
  · intro c; cases c <;> decide
/-- 各善心現前位容得心的聯集。欲善、欲無覆是兩個分開的開關。 -/
def allows (desireGood desireClear : Bool) : Mind12 → Bool
  | .formGood | .formClear | .formlessGood | .learner | .adept => true
  | .desireGood => desireGood
  | .desireClear => desireClear
  | _ => false
def roster (a b : Bool) := minds.filter (allows a b)
theorem sixVersusSeven : (roster false true).length = 6 ∧ (roster true true).length = 7 ∧
    (roster true false).length = 6 := by decide
theorem whichSix (m : Mind12) : allows false true m ≠ allows true false m ↔
    m = .desireGood ∨ m = .desireClear := by cases m <;> decide
theorem sevenIff (a b : Bool) : (roster a b).length = 7 ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

abbrev Grades := Fin 10
theorem partialPossible : (1 : Grades).val < 9 ∧ (1 : Grades).val ≠ 0 := by decide
theorem noPartialPossible : (0 : Grades).val < 9 ∧ (0 : Grades).val = 0 := by decide
theorem noNewGrade (n : Grades) (effectivePath : Prop) (needed : 0 < n.val → effectivePath)
    (blocked : ¬ effectivePath) : n.val = 0 := Nat.eq_zero_of_not_pos (fun pos => blocked (needed pos))

end AbhiLib.Experiments
