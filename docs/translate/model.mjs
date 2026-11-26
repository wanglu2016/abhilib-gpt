// Every displayed formula and every downloadable Lean file uses this signature.
export const signature = `namespace AbhiReading
inductive Realm where | desire | form | formless
inductive Nature where | good | bad | obscured | clear
inductive Level where | first | second | third | fourth
inductive Cut where | seeingSuffering | seeingOrigin | seeingCessation | seeingPath | cultivation | neither
inductive DharmaMark where
  | maturationFruit | karma | karmaPath | volition | visibleElement | visibleBase
  | mind | traineeMind | adeptMind | supernormalResultMind | painFaculty
  | selfView | extremeView | wisdom | ignorance
inductive PersonMark where | noble | nonreturner | arhat
inductive Restraint where | undefiled | meditative

/-- D represents instances of dharmas in the admissible cases under study.
    S represents a person at a particular time, not a timeless individual. -/
structure Reading where
  D : Type
  S : Type
  nature : D → Nature
  binding : D → Option Realm
  born : S → Realm
  cut : D → Cut
  dharmaMark : DharmaMark → D → Prop
  status : PersonMark → S → Prop
  rootLevel : D → Option Level
  withOutflow : D → Prop
  restraint : Restraint → D → Prop
  /-- An admissible adjacent pair, ordered earlier to later, in one continuum. -/
  immediatelyPrecedes : D → D → Prop
  associated : D → D → Prop
  possesses : S → D → Prop
  manifestNow : S → D → Prop
  acquiresNow : S → D → Prop
  practicesByOccurrence : S → D → Prop
  practicesByAcquisition : S → D → Prop
`;
