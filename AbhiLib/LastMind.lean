import AbhiLib.MindClasses
import AbhiLib.Truths

namespace AbhiLib.«最後心論»
open «分別實驗» («十二心»)
open «心類分別» «諦攝»

inductive «無覆無記細類» where
  | «異熟生» | «威儀路» | «工巧處» | «通果»
  deriving DecidableEq

/-- E 為心念個例。無記細類 留空時只知道十二心類別。般涅槃位 專指般涅槃位。 -/
structure «心念論域» (E : Type) where
  «心類» : E → «十二心»
  «無記細類» : E → Option «無覆無記細類»
  «般涅槃位» : E → Prop

variable {E : Type} (c : «心念論域» E)

/-- 文獻規則。般涅槃心可屬威儀路或異熟生；析取並不保證各界兩種俱有。 -/
def «般涅槃心細類» := ∀ e, c.«般涅槃位» e →
  c.«無記細類» e = some .«威儀路» ∨ c.«無記細類» e = some .«異熟生»

/-- 分類約定。帶四種無覆無記細目標記的心必須與其十二心類別一致。 -/
def «無覆細類判攝» := ∀ e k, c.«無記細類» e = some k → «四性判攝» (c.«心類» e) = .«無覆無記»

/-- 在諦攝表中定位一念心。無漏有為心屬聖道。 -/
def «心之諦攝法類» (m : «十二心») : «諦攝法類» :=
  if «有漏» m then .«有漏» else .«聖道»

theorem «有漏心歸有漏法» (m : «十二心») (h : «有漏» m) :
    «心之諦攝法類» m = .«有漏» := by simp [«心之諦攝法類», h]

theorem «最後心無覆無記» (last : «般涅槃心細類» c) (typed : «無覆細類判攝» c) {e : E}
    (h : c.«般涅槃位» e) : «四性判攝» (c.«心類» e) = .«無覆無記» := by
  rcases last e h with hw | hr
  · exact typed e .«威儀路» hw
  · exact typed e .«異熟生» hr

theorem «最後心有漏» (last : «般涅槃心細類» c) (typed : «無覆細類判攝» c) {e : E}
    (h : c.«般涅槃位» e) : «有漏» (c.«心類» e) :=
  «無記心有漏» _ (Or.inr («最後心無覆無記» c last typed h))

theorem «最後心攝苦集二諦» (last : «般涅槃心細類» c) (typed : «無覆細類判攝» c) {e : E}
    (h : c.«般涅槃位» e) : «攝於» («心之諦攝法類» (c.«心類» e)) .«苦諦» ∧
      «攝於» («心之諦攝法類» (c.«心類» e)) .«集諦» :=
  «有漏法攝苦集二諦» («有漏心歸有漏法» _ («最後心有漏» c last typed h))

end AbhiLib.«最後心論»
