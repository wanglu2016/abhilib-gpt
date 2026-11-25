import AbhiLib.Attainment

namespace AbhiLib.Nonreturn
open Attainment

variable (p : PersonState)

/-- 不還果在此時仍成就，則欲界九品修惑已盡。 -/
def fruitCutRule := p.standing = .holding .nonReturn → detached p .desire

/-- 《婆沙》卷一六二，生梵世上。 -/
def higherRule := noble p.standing → ¬ atOrBelowFirst p.birth →
  p.possesses .first .undefiled ∧ ¬ p.possesses .first .mundaneGood ∧
    ¬ p.possesses .first .flavored

/-- 生欲界或梵世，梵世愛盡。 -/
def lowerDetachedRule := noble p.standing → atOrBelowFirst p.birth → detached p .first →
  p.possesses .first .mundaneGood ∧ p.possesses .first .undefiled ∧
    ¬ p.possesses .first .flavored

/-- 生欲界或梵世，下地愛盡而梵世愛未盡。 -/
def lowerAttachedRule := noble p.standing → atOrBelowFirst p.birth → detached p .desire →
  ¬ detached p .first → p.possesses .first .flavored ∧
    p.possesses .first .mundaneGood ∧ p.possesses .first .undefiled

theorem lowerPossessesBoth (gone : lowerDetachedRule p) (remains : lowerAttachedRule p)
    (n : noble p.standing) (b : atOrBelowFirst p.birth) (d : detached p .desire) :
    p.possesses .first .mundaneGood ∧ p.possesses .first .undefiled := by
  by_cases first : detached p .first
  · exact ⟨(gone n b first).1, (gone n b first).2.1⟩
  · exact (remains n b d first).2

theorem detachedNobleFirst (up : higherRule p) (gone : lowerDetachedRule p)
    (remains : lowerAttachedRule p) (n : noble p.standing) (d : detached p .desire) :
    p.possesses .first .undefiled := by
  by_cases low : atOrBelowFirst p.birth
  · exact (lowerPossessesBoth p gone remains n low d).2
  · exact (up n low).1

theorem nonreturnFirstUndefiled (cut : fruitCutRule p) (up : higherRule p)
    (gone : lowerDetachedRule p) (remains : lowerAttachedRule p)
    (f : p.standing = .holding .nonReturn) : p.possesses .first .undefiled :=
  detachedNobleFirst p up gone remains (fruitHolderNoble f) (cut f)

theorem nonreturnFirst (cut : fruitCutRule p) (up : higherRule p)
    (gone : lowerDetachedRule p) (remains : lowerAttachedRule p)
    (f : p.standing = .holding .nonReturn) : hasRoot p .first :=
  ⟨.undefiled, nonreturnFirstUndefiled p cut up gone remains f⟩

theorem higherLacksMundaneFirst (up : higherRule p)
    (n : noble p.standing) (b : ¬ atOrBelowFirst p.birth) : ¬ p.possesses .first .mundaneGood :=
  (up n b).2.1

end AbhiLib.Nonreturn
