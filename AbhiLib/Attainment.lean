namespace AbhiLib.Attainment

inductive Fruit where
  | streamEntry | onceReturn | nonReturn | arhat
  deriving DecidableEq

/-- 記當下已得的最高果；未得初果的聖者另列。 -/
inductive Standing where
  | ordinary | firstPath | holding (fruit : Fruit)
  deriving DecidableEq

def noble (s : Standing) : Prop := s ≠ .ordinary

/-- 生地的九種取值。無漏法的「不繫」不能作為有情的出生地。 -/
inductive BirthPlane where
  | desire | first | second | third | fourth
  | infiniteSpace | infiniteConsciousness | nothingness | neitherPerception
  deriving DecidableEq

abbrev Grades := Fin 10
inductive Level where | first | second | third | fourth deriving DecidableEq
inductive Kind where | flavored | mundaneGood | undefiled deriving DecidableEq

/-- 所有 level 均指根本靜慮。possesses 描述成就，時點由 p 本身指定。 -/
structure PersonState where
  standing : Standing
  birth : BirthPlane
  gradesCut : BirthPlane → Grades
  possesses : Level → Kind → Prop

def detached (p : PersonState) (g : BirthPlane) : Prop := p.gradesCut g = 9

def hasRoot (p : PersonState) (l : Level) : Prop := ∃ k, p.possesses l k

def atOrBelowFirst (b : BirthPlane) : Prop := b = .desire ∨ b = .first

theorem fruitHolderNoble {p : PersonState} {f : Fruit} (h : p.standing = .holding f) :
    noble p.standing := by rw [h]; exact Standing.noConfusion

end AbhiLib.Attainment
