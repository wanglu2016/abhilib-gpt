import AbhiLib.LastMind
import AbhiLib.Nonreturn

namespace AbhiLib.«命題模型»
open «成就論» «不還果論» «最後心論» «諦攝»

/-- 兩念片段。過去的無學道心與最後的欲界威儀心各自分類。 -/
def «最後心模型» : «最後心論».«心念論域» Bool where
  «心類» := fun last => if last then .«欲界無覆心» else .«無學心»
  «無記細類» := fun last => if last then some .«威儀路» else none
  «般涅槃位» := fun last => last = true

def «後繼» (a b : Bool) : Prop := a = false ∧ b = true

theorem «最後心無後繼亦攝集諦» :
    «般涅槃心細類» «最後心模型» ∧ «無覆細類判攝» «最後心模型» ∧ «最後心模型».«般涅槃位» true ∧
    «攝於» («心之諦攝法類» («最後心模型».«心類» true)) .«集諦» ∧
    (¬ ∃ b, «後繼» true b) ∧ «攝於» («心之諦攝法類» («最後心模型».«心類» false)) .«道諦» := by
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
def «生第二靜慮不還者» : «人位» where
  «所居位» := .«持果» .«不還果»
  «生地» := .«第二靜慮»
  «諸地已斷品數» := fun g => if g = .«欲界» ∨ g = .«初靜慮» then 9 else 0
  «成就» := fun l k =>
    (l = .«初靜慮» ∧ k = .«無漏») ∨ l = .«第二靜慮»

theorem «淨初定反例» :
    ∃ p : «人位», «不還果離欲規則» p ∧ «生第二靜慮以上規則» p ∧ «生欲梵而梵愛盡規則» p ∧
      «生欲梵而梵愛未盡規則» p ∧ p.«所居位» = .«持果» .«不還果» ∧
      p.«成就» .«初靜慮» .«無漏» ∧ ¬ p.«成就» .«初靜慮» .«淨» := by
  refine ⟨«生第二靜慮不還者», ?_, ?_, ?_, ?_, rfl, Or.inl ⟨rfl, rfl⟩, ?_⟩
  · intro _; rfl
  · intro _ _
    exact ⟨Or.inl ⟨rfl, rfl⟩, by simp [«生第二靜慮不還者»], by simp [«生第二靜慮不還者»]⟩
  · intro _ h
    rcases h with h | h <;> cases h
  · intro _ h
    rcases h with h | h <;> cases h
  · simp [«生第二靜慮不還者»]


/-- 若只知心屬於無學者，未限定般涅槃位的心類，末念標記仍能落在道心。 -/
theorem «撤般涅槃心規則» :
    ∃ c : «心念論域» Unit, «無覆細類判攝» c ∧ c.«般涅槃位» () ∧
      ¬ «攝於» («心之諦攝法類» (c.«心類» ())) .«集諦» := by
  let c : «心念論域» Unit := ⟨fun _ => .«無學心», fun _ => none, fun _ => True⟩
  refine ⟨c, ?_, True.intro, ?_⟩
  · intro e k h; cases h
  · intro h; cases h

/-- 刪去分類一致性後，無學道心可被錯標為威儀路；另一路便可失敗。 -/
theorem «撤無覆細類一致性» :
    ∃ c : «心念論域» Unit, «般涅槃心細類» c ∧ c.«般涅槃位» () ∧
      ¬ «攝於» («心之諦攝法類» (c.«心類» ())) .«集諦» := by
  let c : «心念論域» Unit := ⟨fun _ => .«無學心», fun _ => some .«威儀路», fun _ => True⟩
  exact ⟨c, fun _ _ => Or.inl rfl, True.intro, fun h => by cases h⟩

/-- 刪除試驗中的四條文獻輸入。每次只改變納入的規則。 -/
inductive «不還果論前提» where | «果» | «上地» | «梵愛盡» | «梵愛未盡» deriving DecidableEq

def «所需前提» (p : «人位») : «不還果論前提» → Prop
  | .«果» => «不還果離欲規則» p
  | .«上地» => «生第二靜慮以上規則» p
  | .«梵愛盡» => «生欲梵而梵愛盡規則» p
  | .«梵愛未盡» => «生欲梵而梵愛未盡規則» p

private def «撤前提模型» (i : «不還果論前提») : «人位» where
  «所居位» := .«持果» .«不還果»
  «生地» := if i = .«上地» then .«第二靜慮» else .«欲界»
  «諸地已斷品數» := fun g => match g with
    | .«欲界» => if i = .«果» then 0 else 9
    | .«初靜慮» => if i = .«梵愛盡» ∨ i = .«上地» then 9 else 0
    | _ => 0
  «成就» := fun _ _ => False

/-- 在本組輸入與本資料型別下，每少一條都有滿足其餘三條的反模型。 -/
theorem «不還果四前提各自必要» (dropped : «不還果論前提») :
    ∃ p : «人位», p.«所居位» = .«持果» .«不還果» ∧
      (∀ i, i ≠ dropped → «所需前提» p i) ∧ ¬ «成就根本靜慮» p .«初靜慮» := by
  refine ⟨«撤前提模型» dropped, rfl, ?_, ?_⟩
  · intro i
    cases dropped <;> cases i <;>
      simp [«所需前提», «不還果離欲規則», «生第二靜慮以上規則», «生欲梵而梵愛盡規則», «生欲梵而梵愛未盡規則»,
        «撤前提模型», «聖者», «欲界或梵世», «已離染»]
  · rintro ⟨k, h⟩
    exact h

end AbhiLib.«命題模型»
