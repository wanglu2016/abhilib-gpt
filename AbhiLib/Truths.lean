namespace AbhiLib.Truths

inductive Truth where | suffering | origin | cessation | path deriving DecidableEq
/-- 此處按有漏、聖道、擇滅及其餘無為分類，見《俱舍論》卷一、二十二。 -/
inductive Domain where
  | withOutflow | noblePath | analyticalCessation | otherUnconditioned
  deriving DecidableEq

/-- 有部諦攝表。苦、集分列為兩種觀察義，同一法可兼屬二諦。 -/
def included (d : Domain) : Truth → Prop
  | .suffering => d = .withOutflow
  | .origin => d = .withOutflow
  | .cessation => d = .analyticalCessation
  | .path => d = .noblePath

theorem bothOfOutflow {d : Domain} (h : d = .withOutflow) :
    included d .suffering ∧ included d .origin := ⟨h, h⟩

end AbhiLib.Truths
