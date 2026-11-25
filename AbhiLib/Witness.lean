import AbhiLib.Article
namespace AbhiLib.Witness
def specimen : Rupa := ⟨.speech,.covered,.first⟩
/-- 欲界見斷有覆心與初定修斷有覆心各一，後者親發有覆語表。 -/
def sample : World where
  admitted x := x = specimen
  Mind := Bool
  Factor := Bool
  Object := Bool
  mc c := if c then .cultivation else .seeing
  fc f := if f then .cultivation else .seeing
  mn _ := .covered
  fnat _ := .covered
  mg c := if c then .first else .desire
  fg f := if f then .first else .desire
  mo c := c
  fo f := f
  door o := if o then .outer else .inner
  kind f := if f then .other else .selfView
  afflicted _ := True
  assoc c f := c = f
  pureMind _ := False
  starts c x := c = true ∧ x = specimen
  vicara c := c = true
  vitarka c := c = true

theorem consistentSample :
    P01 sample ∧ P02 sample ∧ P03 sample ∧ P04 ∧ P05 sample ∧ P06 sample ∧
    P07 sample ∧ P08 sample ∧ P09 sample ∧ P10 sample ∧ P11 ∧ P12 sample ∧
    P13 sample ∧ P14 ∧ P15 sample ∧ P16 sample ∧ B01 sample ∧ B02 sample ∧
    B03 sample ∧ B04 sample ∧ B05 sample ∧
    (∃ x, sample.admitted x ∧ Covered x) ∧ (∃ c, sample.mg c = .desire ∧ sample.mn c = .covered) := by
  simp [P01, P02, P03, P04, P05, P06, P07, P08, P09, P10, P11, P12, P13, P14, P15,
    P16, B01, B02, B03, B04, B05, CanStart, Inward, Outward, TwoViews, FiveViews, GoodOrStained,
    Stain, IsCut, Dyed, ColorKarma, AboveFirst, Low, Manifest, Covered, Neutral,
    sample, specimen, Bool.forall_bool, Bool.exists_bool]
  constructor
  · exact Article.s01
  · intro x _ hx; subst x; rfl
end AbhiLib.Witness
