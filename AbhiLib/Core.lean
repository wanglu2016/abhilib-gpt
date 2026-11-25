namespace AbhiLib

inductive Nature where | good | bad | covered | clear deriving DecidableEq
inductive Ground where | desire | first | second | third | fourth | formless | unbound deriving DecidableEq
inductive Form where | body | speech | unmanifest | other deriving DecidableEq
inductive Cut where | seeing | cultivation | neither deriving DecidableEq
inductive Door where | inner | outer deriving DecidableEq
inductive Kind where | selfView | extremeView | wrongView | graspView | graspRule | ignorance | other
  deriving DecidableEq

structure Rupa where
  form : Form
  nature : Nature
  ground : Ground
  deriving DecidableEq

abbrev Covered (x : Rupa) := x.nature = .covered
abbrev Stain (n : Nature) := n = .bad ∨ n = .covered
abbrev GoodOrStained (n : Nature) := n = .good ∨ Stain n
abbrev Neutral (n : Nature) := n = .covered ∨ n = .clear
abbrev Manifest (x : Rupa) := x.form = .body ∨ x.form = .speech
abbrev ColorKarma (x : Rupa) := Manifest x ∨ x.form = .unmanifest
abbrev Low (g : Ground) := g = .desire ∨ g = .first
abbrev AboveFirst (g : Ground) := ¬ Low g ∧ g ≠ .unbound
abbrev UpperThree (g : Ground) := g = .second ∨ g = .third ∨ g = .fourth
abbrev IsCut (k : Cut) := k ≠ .neither
abbrev TwoViews (k : Kind) := k = .selfView ∨ k = .extremeView
abbrev FiveViews (k : Kind) := TwoViews k ∨ k = .wrongView ∨ k = .graspView ∨ k = .graspRule

/-- 「候選色法」及「此理論所容許的色法」分開。心、心所、所緣是不同論域。 -/
structure World where
  admitted : Rupa → Prop
  Mind : Type
  Factor : Type
  Object : Type
  mc : Mind → Cut
  fc : Factor → Cut
  mn : Mind → Nature
  fnat : Factor → Nature
  mg : Mind → Ground
  fg : Factor → Ground
  mo : Mind → Object
  fo : Factor → Object
  door : Object → Door
  kind : Factor → Kind
  afflicted : Factor → Prop
  assoc : Mind → Factor → Prop
  pureMind : Mind → Prop
  starts : Mind → Rupa → Prop
  vicara : Mind → Prop
  vitarka : Mind → Prop

variable (w : World)
def Inward (c : w.Mind) := w.door (w.mo c) = .inner
def Outward (c : w.Mind) := w.door (w.mo c) = .outer
def CanStart (c : w.Mind) := ∃ x, Manifest x ∧ w.starts c x
def WithView (c : w.Mind) := ∃ f, w.assoc c f ∧ TwoViews (w.kind f)
def WithIgnorance (f : w.Factor) := w.kind f = .ignorance ∧ ∀ c, w.assoc c f → WithView w c
def Dyed (x : Rupa) := ∃ c, w.starts c x ∧ ((x.nature = .good ∧ w.mn c = .good) ∨
  (Stain x.nature ∧ Stain (w.mn c)))

def P01 := ∀ f, w.afflicted f → w.fc f = .seeing → w.door (w.fo f) = .inner
def P02 := ∀ f, FiveViews (w.kind f) → w.fc f = .seeing
def P03 := ∀ c f, w.assoc c f → w.mo c = w.fo f ∧ w.mc c = w.fc f
def P04 := ∀ k : Cut, IsCut k → k = .seeing ∨ k = .cultivation
def P05 := ∀ c, w.mc c = .neither → w.pureMind c
def P06 := ∀ c, ¬ Stain (w.mn c) → w.mc c ≠ .seeing
def P07 := (∀ c, Stain (w.mn c) → ∃ f, w.assoc c f ∧ w.afflicted f) ∧
  (∀ c, w.mn c = .good → ∃ f, w.assoc c f ∧ w.fnat f = .good)
def P08 := ∀ c, CanStart w c → Outward w c
def P09 := ∀ f, w.afflicted f → w.fg f = .desire → w.fnat f = .covered →
  TwoViews (w.kind f) ∨ WithIgnorance w f
def P10 := ∀ x, w.admitted x → GoodOrStained x.nature → Dyed w x ∧ ColorKarma x
def P11 := ∀ x, ColorKarma x ↔ Manifest x ∨ x.form = .unmanifest
def P12 := ∀ c, Outward w c → w.vicara c
def P13 := ∀ c, AboveFirst (w.mg c) → ¬ w.vitarka c ∧ ¬ w.vicara c
def P14 := ∀ n : Nature, n = .bad ∨ n = .covered → Stain n
def P15 := ∀ x, w.admitted x → x.form = .unmanifest → ¬ Neutral x.nature
def P16 := ∀ f, w.afflicted f → IsCut (w.fc f)

/-- 相應惑與心同地、同四分性。 -/
def B01 := ∀ c f, w.assoc c f → w.afflicted f → w.fg f = w.mg c ∧ w.fnat f = w.mn c
/-- 親發有覆表的染心也是有覆，細分有覆、不善。 -/
def B02 := ∀ c x, Manifest x → w.starts c x → Covered x → Stain (w.mn c) → w.mn c = .covered
/-- 表業與直接發心同繫地。 -/
def B03 := ∀ c x, Manifest x → w.starts c x → w.mg c = x.ground
/-- 所容許的每一表業皆有直接發心，涵蓋無覆表。 -/
def B04 := ∀ x, w.admitted x → Manifest x → ∃ c, w.starts c x
/-- 所容許的表業皆有繫地，排除不繫。 -/
def B05 := ∀ x, w.admitted x → Manifest x → x.ground ≠ .unbound

end AbhiLib
