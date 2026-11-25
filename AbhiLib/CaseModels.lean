import AbhiLib.LastMind
import AbhiLib.Nonreturn

namespace AbhiLib.CaseModels
open Attainment Nonreturn LastMind Truths

/-- 兩念片段。過去的無學道心與最後的欲界威儀心各自分類。 -/
def finalExample : LastMind.Context Bool where
  mind := fun last => if last then .desireClear else .adept
  mode := fun last => if last then some .deportment else none
  terminal := fun last => last = true

def next (a b : Bool) : Prop := a = false ∧ b = true

theorem lastWithoutSuccessor :
    terminalModes finalExample ∧ modeTyping finalExample ∧ finalExample.terminal true ∧
    included (domainOfMind (finalExample.mind true)) .origin ∧
    (¬ ∃ b, next true b) ∧ included (domainOfMind (finalExample.mind false)) .path := by
  refine ⟨?_, ?_, rfl, rfl, ?_, rfl⟩
  · intro e h
    change e = true at h
    subst e
    exact Or.inl rfl
  · intro e k h
    cases e
    · cases h
    · rfl
  · rintro ⟨_, h, _⟩
    cases h

/-- 限於本題所用的四條規則，給出一個生第二靜慮的不還者狀態。 -/
def higherExample : PersonState where
  standing := .holding .nonReturn
  birth := .second
  gradesCut := fun g => if g = .desire ∨ g = .first then 9 else 0
  possesses := fun l k =>
    (l = .first ∧ k = .undefiled) ∨ l = .second

theorem higherCounterexample :
    ∃ p : PersonState, fruitCutRule p ∧ higherRule p ∧ lowerDetachedRule p ∧
      lowerAttachedRule p ∧ p.standing = .holding .nonReturn ∧
      p.possesses .first .undefiled ∧ ¬ p.possesses .first .mundaneGood := by
  refine ⟨higherExample, ?_, ?_, ?_, ?_, rfl, Or.inl ⟨rfl, rfl⟩, ?_⟩
  · intro _; rfl
  · intro _ _
    exact ⟨Or.inl ⟨rfl, rfl⟩, by simp [higherExample], by simp [higherExample]⟩
  · intro _ h
    rcases h with h | h <;> cases h
  · intro _ h
    rcases h with h | h <;> cases h
  · simp [higherExample]


/-- 若只知心屬於無學者，未限定般涅槃位的心類，末念標記仍能落在道心。 -/
theorem missingTerminalRule :
    ∃ c : Context Unit, modeTyping c ∧ c.terminal () ∧
      ¬ included (domainOfMind (c.mind ())) .origin := by
  let c : Context Unit := ⟨fun _ => .adept, fun _ => none, fun _ => True⟩
  refine ⟨c, ?_, True.intro, ?_⟩
  · intro e k h; cases h
  · intro h; cases h

/-- 刪去分類一致性後，無學道心可被錯標為威儀路；另一路便可失敗。 -/
theorem missingModeTyping :
    ∃ c : Context Unit, terminalModes c ∧ c.terminal () ∧
      ¬ included (domainOfMind (c.mind ())) .origin := by
  let c : Context Unit := ⟨fun _ => .adept, fun _ => some .deportment, fun _ => True⟩
  exact ⟨c, fun _ _ => Or.inl rfl, True.intro, fun h => by cases h⟩

/-- 刪除試驗中的四條文獻輸入。每次只改變納入的規則。 -/
inductive Input where | fruit | upper | exhausted | remaining deriving DecidableEq

def required (p : PersonState) : Input → Prop
  | .fruit => fruitCutRule p
  | .upper => higherRule p
  | .exhausted => lowerDetachedRule p
  | .remaining => lowerAttachedRule p

private def omission (i : Input) : PersonState where
  standing := .holding .nonReturn
  birth := if i = .upper then .second else .desire
  gradesCut := fun g => match g with
    | .desire => if i = .fruit then 0 else 9
    | .first => if i = .exhausted ∨ i = .upper then 9 else 0
    | _ => 0
  possesses := fun _ _ => False

/-- 在本組輸入與本資料型別下，每少一條都有滿足其餘三條的反模型。 -/
theorem eachNonreturnInputNeeded (dropped : Input) :
    ∃ p : PersonState, p.standing = .holding .nonReturn ∧
      (∀ i, i ≠ dropped → required p i) ∧ ¬ hasRoot p .first := by
  refine ⟨omission dropped, rfl, ?_, ?_⟩
  · intro i
    cases dropped <;> cases i <;>
      simp [required, fruitCutRule, higherRule, lowerDetachedRule, lowerAttachedRule,
        omission, noble, atOrBelowFirst, detached]
  · rintro ⟨k, h⟩
    exact h

end AbhiLib.CaseModels
