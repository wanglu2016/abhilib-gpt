import AbhiLib.MindClasses
import AbhiLib.Truths

namespace AbhiLib.LastMind
open Experiments (Mind12)
open MindClasses Truths

inductive ClearMode where
  | maturation | deportment | craft | supernormalResult
  deriving DecidableEq

/-- E 為心念個例。mode 留空時只知道十二心類別。terminal 專指般涅槃位。 -/
structure Context (E : Type) where
  mind : E → Mind12
  mode : E → Option ClearMode
  terminal : E → Prop

variable {E : Type} (c : Context E)

/-- 文獻規則。般涅槃心可屬威儀路或異熟生；析取並不保證各界兩種俱有。 -/
def terminalModes := ∀ e, c.terminal e →
  c.mode e = some .deportment ∨ c.mode e = some .maturation

/-- 分類約定。帶四種無覆無記細目標記的心必須與其十二心類別一致。 -/
def modeTyping := ∀ e k, c.mode e = some k → nature (c.mind e) = .clear

/-- 在諦攝表中定位一念心。無漏有為心屬聖道。 -/
def domainOfMind (m : Mind12) : Domain :=
  if withOutflow m then .withOutflow else .noblePath

theorem domainOfOutflow (m : Mind12) (h : withOutflow m) :
    domainOfMind m = .withOutflow := by simp [domainOfMind, h]

theorem finalClear (last : terminalModes c) (typed : modeTyping c) {e : E}
    (h : c.terminal e) : nature (c.mind e) = .clear := by
  rcases last e h with hw | hr
  · exact typed e .deportment hw
  · exact typed e .maturation hr

theorem finalWithOutflow (last : terminalModes c) (typed : modeTyping c) {e : E}
    (h : c.terminal e) : withOutflow (c.mind e) :=
  neutralWithOutflow _ (Or.inr (finalClear c last typed h))

theorem finalBothTruths (last : terminalModes c) (typed : modeTyping c) {e : E}
    (h : c.terminal e) : included (domainOfMind (c.mind e)) .suffering ∧
      included (domainOfMind (c.mind e)) .origin :=
  bothOfOutflow (domainOfOutflow _ (finalWithOutflow c last typed h))

end AbhiLib.LastMind
