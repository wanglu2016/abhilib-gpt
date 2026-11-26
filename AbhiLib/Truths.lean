namespace AbhiLib.«諦攝»

inductive «四諦» where | «苦諦» | «集諦» | «滅諦» | «道諦» deriving DecidableEq
/-- 此處按有漏、聖道、擇滅及其餘無為分類，見《俱舍論》卷一、二十二。 -/
inductive «諦攝法類» where
  | «有漏» | «聖道» | «擇滅» | «其餘無為»
  deriving DecidableEq

/-- 有部諦攝表。苦、集分列為兩種觀察義，同一法可兼屬二諦。 -/
def «攝於» (d : «諦攝法類») : «四諦» → Prop
  | .«苦諦» => d = .«有漏»
  | .«集諦» => d = .«有漏»
  | .«滅諦» => d = .«擇滅»
  | .«道諦» => d = .«聖道»

theorem «有漏法攝苦集二諦» {d : «諦攝法類»} (h : d = .«有漏») :
    «攝於» d .«苦諦» ∧ «攝於» d .«集諦» := ⟨h, h⟩

end AbhiLib.«諦攝»
