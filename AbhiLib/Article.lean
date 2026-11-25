import AbhiLib.Core
namespace AbhiLib.Article
variable (w : World)

theorem s01 : P04 := by intro k h; cases k <;> simp_all [IsCut]
theorem s02 (p : P05 w) : P05 w := p
theorem s03 (p : P05 w) (c : w.Mind) (h : ¬ w.pureMind c) : IsCut (w.mc c) := fun e => h (s02 w p c e)
theorem s04 (p : P05 w) (c : w.Mind) (h : ¬ w.pureMind c) :
    w.mc c = .seeing ∨ w.mc c = .cultivation := s01 _ (s03 w p c h)
theorem s05 (p : P06 w) : P06 w := p
theorem s06 (p : P06 w) (c : w.Mind) (h : w.mc c = .seeing) : Stain (w.mn c) := by
  by_cases s : Stain (w.mn c)
  · exact s
  · exact False.elim (s05 w p c s h)
theorem s07 (p : P07 w) : P07 w := p
theorem s08 (p6 : P06 w) (p7 : P07 w) (c : w.Mind) (h : w.mc c = .seeing) :
    ∃ f, w.assoc c f ∧ w.afflicted f := (s07 w p7).1 c (s06 w p6 c h)
theorem s09 (p : P16 w) : P16 w := p
theorem s10 (p : P16 w) (f : w.Factor) (a : w.afflicted f) :
    w.fc f = .seeing ∨ w.fc f = .cultivation := s01 _ (s09 w p f a)
theorem s11 (p : P03 w) (c : w.Mind) (f : w.Factor) (a : w.assoc c f) (h : w.fc f = .cultivation) :
    w.mc c = .cultivation := (p c f a).2.trans h
theorem s12 (k : Cut) (h : k = .seeing) : k ≠ .cultivation := by simp [h]
theorem s13 (p : P03 w) (c : w.Mind) (f : w.Factor) (h : w.mc c = .seeing) (r : w.fc f = .cultivation) :
    ¬ w.assoc c f := fun a => s12 _ h (s11 w p c f a r)
def HasSeeing := ∀ c, w.mc c = .seeing → ∃ f, w.assoc c f ∧ w.afflicted f ∧ w.fc f = .seeing
theorem s14 (p3 : P03 w) (p6 : P06 w) (p7 : P07 w) (p16 : P16 w) : HasSeeing w := by
  intro c h
  obtain ⟨f,a,o⟩ := s08 w p6 p7 c h
  exact ⟨f,a,o,(s10 w p16 f o).resolve_right (fun r => s13 w p3 c f h r a)⟩
theorem s15 (p : P01 w) : P01 w := p
theorem s16 (h : HasSeeing w) : HasSeeing w := h
theorem s17 (p : P03 w) (c : w.Mind) (f : w.Factor) (a : w.assoc c f) : w.mo c = w.fo f := (p c f a).1
theorem s18 (p1 : P01 w) (p3 : P03 w) (seen : HasSeeing w) (c : w.Mind) (h : w.mc c = .seeing) :
    w.door (w.mo c) = .inner := by
  obtain ⟨f,a,o,cut⟩ := s16 w seen c h
  rw [s17 w p3 c f a]; exact s15 w p1 f o cut
theorem s19 (p1 : P01 w) (p3 : P03 w) (seen : HasSeeing w) (c : w.Mind) (h : w.mc c = .seeing) :
    Inward w c := s18 w p1 p3 seen c h
theorem s20 (p : P08 w) : P08 w := p
theorem s21 (p : P08 w) (c : w.Mind) (h : Inward w c) : ¬ CanStart w c :=
  fun a => Door.noConfusion (h.symm.trans (s20 w p c a))
theorem s22 (p1 : P01 w) (p3 : P03 w) (p8 : P08 w) (seen : HasSeeing w) (c : w.Mind)
    (h : w.mc c = .seeing) : ¬ CanStart w c := s21 w p8 c (s19 w p1 p3 seen c h)
theorem s23 (p : P09 w) : P09 w := p
theorem s24 (p7 : P07 w) (p9 : P09 w) (b : B01 w) (c : w.Mind) (d : w.mg c = .desire)
    (n : w.mn c = .covered) : WithView w c := by
  obtain ⟨f,a,o⟩ := (s07 w p7).1 c (Or.inr n)
  obtain ⟨fg,fn⟩ := b c f a o
  rcases s23 w p9 f o (fg.trans d) (fn.trans n) with view | ignorance
  · exact ⟨f,a,view⟩
  · exact ignorance.2 c a
theorem s25 (p : P02 w) (f : w.Factor) (h : TwoViews (w.kind f)) : w.fc f = .seeing := p f (Or.inl h)
theorem s26 (p2 : P02 w) (p3 : P03 w) (p7 : P07 w) (p9 : P09 w) (b : B01 w)
    (c : w.Mind) (d : w.mg c = .desire) (n : w.mn c = .covered) : w.mc c = .seeing := by
  obtain ⟨f,a,view⟩ := s24 w p7 p9 b c d n
  exact (p3 c f a).2.trans (s25 w p2 f view)
def Block := ∀ c, w.mg c = .desire → w.mn c = .covered → ¬ CanStart w c
theorem s27 (seen : ∀ c, w.mg c = .desire → w.mn c = .covered → w.mc c = .seeing)
    (block : ∀ c, w.mc c = .seeing → ¬ CanStart w c) : Block w := fun c d n => block c (seen c d n)
theorem s28 (block : Block w) (b : B03 w) (x : Rupa) (m : Manifest x) (d : x.ground = .desire)
    (c : w.Mind) (n : w.mn c = .covered) : ¬ w.starts c x :=
  fun h => block c ((b c x m h).trans d) n ⟨x,m,h⟩
theorem s29 (p : P10 w) (x : Rupa) (a : w.admitted x) (n : GoodOrStained x.nature) : Dyed w x := (p x a n).1
def s30 (x : {r : Rupa // Manifest r}) : Rupa := x.val
theorem s31 (p : P10 w) (x : {r : Rupa // Manifest r}) (a : w.admitted x.val)
    (n : GoodOrStained x.val.nature) : Dyed w x.val := s29 w p (s30 x) a n
theorem s32 (block : Block w) (b2 : B02 w) (b3 : B03 w) (p : P10 w) (x : Rupa)
    (a : w.admitted x) (m : Manifest x) (d : x.ground = .desire) : ¬ Covered x := by
  intro cov
  obtain ⟨c,h,agree⟩ := s31 w p ⟨x,m⟩ a (Or.inr (Or.inr cov))
  rcases agree with good | stained
  · exact Nature.noConfusion (good.1.symm.trans cov)
  · exact s28 w block b3 x m d c (b2 c x m h cov stained.2) h
theorem s33 (block : Block w) (b2 : B02 w) (b3 : B03 w) (p : P10 w) (x : Rupa)
    (a : w.admitted x) (m : Manifest x) (cov : Covered x) : x.ground ≠ .desire :=
  fun d => s32 w block b2 b3 p x a m d cov
theorem s34 (p8 : P08 w) (p12 : P12 w) (c : w.Mind) (a : CanStart w c) : w.vicara c := p12 c (p8 c a)
theorem s35 (p : P13 w) : P13 w := p
theorem s36 (p8 : P08 w) (p12 : P12 w) (p13 : P13 w) (b3 : B03 w) (b4 : B04 w)
    (x : Rupa) (a : w.admitted x) (upper : AboveFirst x.ground) : ¬ Manifest x := by
  intro m
  obtain ⟨c,h⟩ := b4 x a m
  have loc := b3 c x m h
  exact (s35 w p13 c (loc.symm ▸ upper)).2 (s34 w p8 p12 c ⟨x,m,h⟩)
theorem s37 (x : Rupa) (noUpper : AboveFirst x.ground → ¬ Manifest x) (bound : B05 w)
    (a : w.admitted x) (m : Manifest x) : Low x.ground := by
  by_cases l : Low x.ground
  · exact l
  · exact False.elim (noUpper ⟨l,bound x a m⟩ m)
theorem s38 (x : Rupa) (noDesire : x.ground ≠ .desire) (l : Low x.ground) : x.ground = .first :=
  l.resolve_left noDesire
theorem s39 (p : P10 w) (x : Rupa) (a : w.admitted x) (s : Stain x.nature) : Dyed w x := (p x a (Or.inr s)).1
theorem s40 (x : Rupa) (c : Covered x) : Stain x.nature := Or.inr c
theorem s41 (p : P10 w) (x : Rupa) (a : w.admitted x) (c : Covered x) : Dyed w x := s39 w p x a (s40 x c)
theorem s42 (p : P15 w) (x : Rupa) (a : w.admitted x) (u : x.form = .unmanifest) : ¬ Neutral x.nature := p x a u
theorem s43 (p : P15 w) (x : Rupa) (a : w.admitted x) (c : Covered x) : x.form ≠ .unmanifest :=
  fun u => s42 w p x a u (Or.inl c)
theorem s44 (p : P10 w) (x : Rupa) (a : w.admitted x) (n : GoodOrStained x.nature) : ColorKarma x := (p x a n).2
theorem s45 (p : P10 w) (x : Rupa) (a : w.admitted x) (c : Covered x) : ColorKarma x :=
  s44 w p x a (Or.inr (s40 x c))
theorem s46 (x : Rupa) (k : ColorKarma x) (h : x.form ≠ .unmanifest) : Manifest x := k.resolve_right h
theorem s47 (x : Rupa) (c : Covered x) (m : Manifest x) : Covered x ∧ Manifest x := ⟨c,m⟩
theorem s48 (x : Rupa) (h : Covered x → Manifest x → x.ground = .first)
    (cm : Covered x ∧ Manifest x) : x.ground = .first := h cm.1 cm.2

/-- 接合後三段。將第三步的中間結果作參數，兩條長證可共用以下證明。 -/
theorem assemble (p1 : P01 w) (p2 : P02 w) (p3 : P03 w) (p7 : P07 w) (p8 : P08 w)
    (p9 : P09 w) (p10 : P10 w) (p12 : P12 w) (p13 : P13 w) (p15 : P15 w)
    (b1 : B01 w) (b2 : B02 w) (b3 : B03 w) (b4 : B04 w) (b5 : B05 w) (seen : HasSeeing w)
    (x : Rupa) (a : w.admitted x) (c : Covered x) : x.ground = .first := by
  have block := s27 w (s26 w p2 p3 p7 p9 b1) (s22 w p1 p3 p8 seen)
  have h (cov : Covered x) (m : Manifest x) : x.ground = .first :=
    s38 x (s33 w block b2 b3 p10 x a m cov) (s37 w x (s36 w p8 p12 p13 b3 b4 x a) b5 a m)
  exact s48 x h (s47 x c (s46 x (s45 w p10 x a c) (s43 w p15 x a c)))

theorem articleOnlyFirst (p1 : P01 w) (p2 : P02 w) (p3 : P03 w) (p6 : P06 w) (p7 : P07 w)
    (p8 : P08 w) (p9 : P09 w) (p10 : P10 w) (p12 : P12 w) (p13 : P13 w) (p15 : P15 w)
    (p16 : P16 w) (b1 : B01 w) (b2 : B02 w) (b3 : B03 w) (b4 : B04 w) (b5 : B05 w)
    (x : Rupa) (a : w.admitted x) (c : Covered x) : x.ground = .first :=
  assemble w p1 p2 p3 p7 p8 p9 p10 p12 p13 p15 b1 b2 b3 b4 b5 (s14 w p3 p6 p7 p16) x a c

theorem seeingDirect (p3 : P03 w) (p6 : P06 w) (p7 : P07 w) : HasSeeing w := by
  intro c h
  obtain ⟨f,assoc,aff⟩ := s08 w p6 p7 c h
  exact ⟨f,assoc,aff,(p3 c f assoc).2.symm.trans h⟩

theorem withoutP16 (p1 : P01 w) (p2 : P02 w) (p3 : P03 w) (p6 : P06 w) (p7 : P07 w)
    (p8 : P08 w) (p9 : P09 w) (p10 : P10 w) (p12 : P12 w) (p13 : P13 w) (p15 : P15 w)
    (b1 : B01 w) (b2 : B02 w) (b3 : B03 w) (b4 : B04 w) (b5 : B05 w)
    (x : Rupa) (a : w.admitted x) (c : Covered x) : x.ground = .first :=
  assemble w p1 p2 p3 p7 p8 p9 p10 p12 p13 p15 b1 b2 b3 b4 b5 (seeingDirect w p3 p6 p7) x a c

end AbhiLib.Article
