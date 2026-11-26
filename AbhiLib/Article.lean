import AbhiLib.Core
namespace AbhiLib.«本證»
variable (w : «論域»)

theorem s01 : P04 := by intro k h; cases k <;> simp_all [«所斷»]
theorem s02 (p : P05 w) : P05 w := p
theorem s03 (p : P05 w) (c : w.«心») (h : ¬ w.«無漏心» c) : «所斷» (w.«心斷類» c) := fun e => h (s02 w p c e)
theorem s04 (p : P05 w) (c : w.«心») (h : ¬ w.«無漏心» c) :
    w.«心斷類» c = .«見所斷» ∨ w.«心斷類» c = .«修所斷» := s01 _ (s03 w p c h)
theorem s05 (p : P06 w) : P06 w := p
theorem s06 (p : P06 w) (c : w.«心») (h : w.«心斷類» c = .«見所斷») : «染» (w.«心性» c) := by
  by_cases s : «染» (w.«心性» c)
  · exact s
  · exact False.elim (s05 w p c s h)
theorem s07 (p : P07 w) : P07 w := p
theorem s08 (p6 : P06 w) (p7 : P07 w) (c : w.«心») (h : w.«心斷類» c = .«見所斷») :
    ∃ f, w.«相應» c f ∧ w.«是惑» f := (s07 w p7).1 c (s06 w p6 c h)
theorem s09 (p : P16 w) : P16 w := p
theorem s10 (p : P16 w) (f : w.«心所») (a : w.«是惑» f) :
    w.«心所斷類» f = .«見所斷» ∨ w.«心所斷類» f = .«修所斷» := s01 _ (s09 w p f a)
theorem s11 (p : P03 w) (c : w.«心») (f : w.«心所») (a : w.«相應» c f) (h : w.«心所斷類» f = .«修所斷») :
    w.«心斷類» c = .«修所斷» := (p c f a).2.trans h
theorem s12 (k : «斷類») (h : k = .«見所斷») : k ≠ .«修所斷» := by simp [h]
theorem s13 (p : P03 w) (c : w.«心») (f : w.«心所») (h : w.«心斷類» c = .«見所斷») (r : w.«心所斷類» f = .«修所斷») :
    ¬ w.«相應» c f := fun a => s12 _ h (s11 w p c f a r)
def «見斷心與見斷惑相應» := ∀ c, w.«心斷類» c = .«見所斷» → ∃ f, w.«相應» c f ∧ w.«是惑» f ∧ w.«心所斷類» f = .«見所斷»
theorem s14 (p3 : P03 w) (p6 : P06 w) (p7 : P07 w) (p16 : P16 w) : «見斷心與見斷惑相應» w := by
  intro c h
  obtain ⟨f,a,o⟩ := s08 w p6 p7 c h
  exact ⟨f,a,o,(s10 w p16 f o).resolve_right (fun r => s13 w p3 c f h r a)⟩
theorem s15 (p : P01 w) : P01 w := p
theorem s16 (h : «見斷心與見斷惑相應» w) : «見斷心與見斷惑相應» w := h
theorem s17 (p : P03 w) (c : w.«心») (f : w.«心所») (a : w.«相應» c f) : w.«心之所緣» c = w.«心所之所緣» f := (p c f a).1
theorem s18 (p1 : P01 w) (p3 : P03 w) (seen : «見斷心與見斷惑相應» w) (c : w.«心») (h : w.«心斷類» c = .«見所斷») :
    w.«所緣之門» (w.«心之所緣» c) = .«內門» := by
  obtain ⟨f,a,o,cut⟩ := s16 w seen c h
  rw [s17 w p3 c f a]; exact s15 w p1 f o cut
theorem s19 (p1 : P01 w) (p3 : P03 w) (seen : «見斷心與見斷惑相應» w) (c : w.«心») (h : w.«心斷類» c = .«見所斷») :
    «內門轉» w c := s18 w p1 p3 seen c h
theorem s20 (p : P08 w) : P08 w := p
theorem s21 (p : P08 w) (c : w.«心») (h : «內門轉» w c) : ¬ «能發表» w c :=
  fun a => «所緣門».noConfusion (h.symm.trans (s20 w p c a))
theorem s22 (p1 : P01 w) (p3 : P03 w) (p8 : P08 w) (seen : «見斷心與見斷惑相應» w) (c : w.«心»)
    (h : w.«心斷類» c = .«見所斷») : ¬ «能發表» w c := s21 w p8 c (s19 w p1 p3 seen c h)
theorem s23 (p : P09 w) : P09 w := p
theorem s24 (p7 : P07 w) (p9 : P09 w) (b : B01 w) (c : w.«心») (d : w.«心繫屬» c = .«欲界»)
    (n : w.«心性» c = .«有覆無記») : «與身邊見相應» w c := by
  obtain ⟨f,a,o⟩ := (s07 w p7).1 c (Or.inr n)
  obtain ⟨«心所繫屬»,fn⟩ := b c f a o
  rcases s23 w p9 f o («心所繫屬».trans d) (fn.trans n) with view | «無明»
  · exact ⟨f,a,view⟩
  · exact «無明».2 c a
theorem s25 (p : P02 w) (f : w.«心所») (h : «身邊二見» (w.«心所種類» f)) : w.«心所斷類» f = .«見所斷» := p f (Or.inl h)
theorem s26 (p2 : P02 w) (p3 : P03 w) (p7 : P07 w) (p9 : P09 w) (b : B01 w)
    (c : w.«心») (d : w.«心繫屬» c = .«欲界») (n : w.«心性» c = .«有覆無記») : w.«心斷類» c = .«見所斷» := by
  obtain ⟨f,a,view⟩ := s24 w p7 p9 b c d n
  exact (p3 c f a).2.trans (s25 w p2 f view)
def «欲界有覆心不能發表» := ∀ c, w.«心繫屬» c = .«欲界» → w.«心性» c = .«有覆無記» → ¬ «能發表» w c
theorem s27 (seen : ∀ c, w.«心繫屬» c = .«欲界» → w.«心性» c = .«有覆無記» → w.«心斷類» c = .«見所斷»)
    (block : ∀ c, w.«心斷類» c = .«見所斷» → ¬ «能發表» w c) : «欲界有覆心不能發表» w := fun c d n => block c (seen c d n)
theorem s28 (block : «欲界有覆心不能發表» w) (b : B03 w) (x : «色法») (m : «表色» x) (d : x.«繫屬» = .«欲界»)
    (c : w.«心») (n : w.«心性» c = .«有覆無記») : ¬ w.«等起» c x :=
  fun h => block c ((b c x m h).trans d) n ⟨x,m,h⟩
theorem s29 (p : P10 w) (x : «色法») (a : w.«容許色法» x) (n : «善或染» x.«四性判攝») : «由等起成善染» w x := (p x a n).1
def s30 (x : {r : «色法» // «表色» r}) : «色法» := x.val
theorem s31 (p : P10 w) (x : {r : «色法» // «表色» r}) (a : w.«容許色法» x.val)
    (n : «善或染» x.val.«四性判攝») : «由等起成善染» w x.val := s29 w p (s30 x) a n
theorem s32 (block : «欲界有覆心不能發表» w) (b2 : B02 w) (b3 : B03 w) (p : P10 w) (x : «色法»)
    (a : w.«容許色法» x) (m : «表色» x) (d : x.«繫屬» = .«欲界») : ¬ «有覆無記色» x := by
  intro cov
  obtain ⟨c,h,agree⟩ := s31 w p ⟨x,m⟩ a (Or.inr (Or.inr cov))
  rcases agree with «善» | stained
  · exact «四性».noConfusion («善».1.symm.trans cov)
  · exact s28 w block b3 x m d c (b2 c x m h cov stained.2) h
theorem s33 (block : «欲界有覆心不能發表» w) (b2 : B02 w) (b3 : B03 w) (p : P10 w) (x : «色法»)
    (a : w.«容許色法» x) (m : «表色» x) (cov : «有覆無記色» x) : x.«繫屬» ≠ .«欲界» :=
  fun d => s32 w block b2 b3 p x a m d cov
theorem s34 (p8 : P08 w) (p12 : P12 w) (c : w.«心») (a : «能發表» w c) : w.«伺» c := p12 c (p8 c a)
theorem s35 (p : P13 w) : P13 w := p
theorem s36 (p8 : P08 w) (p12 : P12 w) (p13 : P13 w) (b3 : B03 w) (b4 : B04 w)
    (x : «色法») (a : w.«容許色法» x) («上地» : «高於初靜慮之繫地» x.«繫屬») : ¬ «表色» x := by
  intro m
  obtain ⟨c,h⟩ := b4 x a m
  have loc := b3 c x m h
  exact (s35 w p13 c (loc.symm ▸ «上地»)).2 (s34 w p8 p12 c ⟨x,m,h⟩)
theorem s37 (x : «色法») (noUpper : «高於初靜慮之繫地» x.«繫屬» → ¬ «表色» x) (bound : B05 w)
    (a : w.«容許色法» x) (m : «表色» x) : «欲界或初靜慮» x.«繫屬» := by
  by_cases l : «欲界或初靜慮» x.«繫屬»
  · exact l
  · exact False.elim (noUpper ⟨l,bound x a m⟩ m)
theorem s38 (x : «色法») (noDesire : x.«繫屬» ≠ .«欲界») (l : «欲界或初靜慮» x.«繫屬») : x.«繫屬» = .«初靜慮» :=
  l.resolve_left noDesire
theorem s39 (p : P10 w) (x : «色法») (a : w.«容許色法» x) (s : «染» x.«四性判攝») : «由等起成善染» w x := (p x a (Or.inr s)).1
theorem s40 (x : «色法») (c : «有覆無記色» x) : «染» x.«四性判攝» := Or.inr c
theorem s41 (p : P10 w) (x : «色法») (a : w.«容許色法» x) (c : «有覆無記色» x) : «由等起成善染» w x := s39 w p x a (s40 x c)
theorem s42 (p : P15 w) (x : «色法») (a : w.«容許色法» x) (u : x.«種類» = .«無表») : ¬ «無記» x.«四性判攝» := p x a u
theorem s43 (p : P15 w) (x : «色法») (a : w.«容許色法» x) (c : «有覆無記色» x) : x.«種類» ≠ .«無表» :=
  fun u => s42 w p x a u (Or.inl c)
theorem s44 (p : P10 w) (x : «色法») (a : w.«容許色法» x) (n : «善或染» x.«四性判攝») : «色業» x := (p x a n).2
theorem s45 (p : P10 w) (x : «色法») (a : w.«容許色法» x) (c : «有覆無記色» x) : «色業» x :=
  s44 w p x a (Or.inr (s40 x c))
theorem s46 (x : «色法») (k : «色業» x) (h : x.«種類» ≠ .«無表») : «表色» x := k.resolve_right h
theorem s47 (x : «色法») (c : «有覆無記色» x) (m : «表色» x) : «有覆無記色» x ∧ «表色» x := ⟨c,m⟩
theorem s48 (x : «色法») (h : «有覆無記色» x → «表色» x → x.«繫屬» = .«初靜慮»)
    (cm : «有覆無記色» x ∧ «表色» x) : x.«繫屬» = .«初靜慮» := h cm.1 cm.2

/-- 接合後三段。將第三步的中間結果作參數，兩條長證可共用以下證明。 -/
theorem «五段長證» (p1 : P01 w) (p2 : P02 w) (p3 : P03 w) (p7 : P07 w) (p8 : P08 w)
    (p9 : P09 w) (p10 : P10 w) (p12 : P12 w) (p13 : P13 w) (p15 : P15 w)
    (b1 : B01 w) (b2 : B02 w) (b3 : B03 w) (b4 : B04 w) (b5 : B05 w) (seen : «見斷心與見斷惑相應» w)
    (x : «色法») (a : w.«容許色法» x) (c : «有覆無記色» x) : x.«繫屬» = .«初靜慮» := by
  have block := s27 w (s26 w p2 p3 p7 p9 b1) (s22 w p1 p3 p8 seen)
  have h (cov : «有覆無記色» x) (m : «表色» x) : x.«繫屬» = .«初靜慮» :=
    s38 x (s33 w block b2 b3 p10 x a m cov) (s37 w x (s36 w p8 p12 p13 b3 b4 x a) b5 a m)
  exact s48 x h (s47 x c (s46 x (s45 w p10 x a c) (s43 w p15 x a c)))

theorem «有覆無記色唯初靜慮繫» (p1 : P01 w) (p2 : P02 w) (p3 : P03 w) (p6 : P06 w) (p7 : P07 w)
    (p8 : P08 w) (p9 : P09 w) (p10 : P10 w) (p12 : P12 w) (p13 : P13 w) (p15 : P15 w)
    (p16 : P16 w) (b1 : B01 w) (b2 : B02 w) (b3 : B03 w) (b4 : B04 w) (b5 : B05 w)
    (x : «色法») (a : w.«容許色法» x) (c : «有覆無記色» x) : x.«繫屬» = .«初靜慮» :=
  «五段長證» w p1 p2 p3 p7 p8 p9 p10 p12 p13 p15 b1 b2 b3 b4 b5 (s14 w p3 p6 p7 p16) x a c

theorem «由同斷得見斷相應» (p3 : P03 w) (p6 : P06 w) (p7 : P07 w) : «見斷心與見斷惑相應» w := by
  intro c h
  obtain ⟨f,«相應»,aff⟩ := s08 w p6 p7 c h
  exact ⟨f,«相應»,aff,(p3 c f «相應»).2.symm.trans h⟩

theorem «省前提十六之長證» (p1 : P01 w) (p2 : P02 w) (p3 : P03 w) (p6 : P06 w) (p7 : P07 w)
    (p8 : P08 w) (p9 : P09 w) (p10 : P10 w) (p12 : P12 w) (p13 : P13 w) (p15 : P15 w)
    (b1 : B01 w) (b2 : B02 w) (b3 : B03 w) (b4 : B04 w) (b5 : B05 w)
    (x : «色法») (a : w.«容許色法» x) (c : «有覆無記色» x) : x.«繫屬» = .«初靜慮» :=
  «五段長證» w p1 p2 p3 p7 p8 p9 p10 p12 p13 p15 b1 b2 b3 b4 b5 («由同斷得見斷相應» w p3 p6 p7) x a c

end AbhiLib.«本證»
