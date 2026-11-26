import AbhiLib.Article
import AbhiLib.MindClasses
import AbhiLib.Attainment
namespace AbhiLib.«分別實驗»

abbrev «染色屬業» (x : «色法») := «染» x.«四性判攝» → «色業» x
abbrev «無表有記» (x : «色法») := x.«種類» = .«無表» → ¬ «無記» x.«四性判攝»
abbrev «表業繫地» (x : «色法») := «表色» x → «欲界或初靜慮» x.«繫屬»
abbrev «欲界無有覆表» (x : «色法») := «表色» x → «有覆無記色» x → x.«繫屬» ≠ .«欲界»
abbrev «有餘師表業繫地» (x : «色法») := «表色» x → «欲界或初靜慮» x.«繫屬» ∨ («上三靜慮» x.«繫屬» ∧ x.«四性判攝» = .«無覆無記»)
abbrev «四規則皆成立» (x : «色法») := «染色屬業» x ∧ «無表有記» x ∧ «表業繫地» x ∧ «欲界無有覆表» x
abbrev «有覆色異地反例» (x : «色法») := «有覆無記色» x ∧ x.«繫屬» ≠ .«初靜慮»

theorem «有覆無記色是表» (x : «色法») (k : «染色屬業» x) (a : «無表有記» x) (c : «有覆無記色» x) : «表色» x :=
  (k (Or.inr c)).resolve_right (fun u => a u (Or.inl c))

theorem «由四規則得初定繫» (x : «色法») (k : «染色屬業» x) (a : «無表有記» x) (g : «表業繫地» x) (d : «欲界無有覆表» x) (c : «有覆無記色» x) :
    x.«繫屬» = .«初靜慮» := (g («有覆無記色是表» x k a c)).resolve_left (d («有覆無記色是表» x k a c) c)

theorem «有餘師亦唯初定» (x : «色法») (k : «染色屬業» x) (a : «無表有記» x) (g : «有餘師表業繫地» x) (d : «欲界無有覆表» x) (c : «有覆無記色» x) :
    x.«繫屬» = .«初靜慮» := by
  have m := «有覆無記色是表» x k a c
  rcases g m with low | «上地»
  · exact low.resolve_left (d m c)
  · exact False.elim («四性».noConfusion (c.symm.trans «上地».2))

theorem «二說差例» : ∃ x : «色法», «染色屬業» x ∧ «無表有記» x ∧ «欲界無有覆表» x ∧ «有餘師表業繫地» x ∧ ¬ «表業繫地» x := by
  exact ⟨⟨.«語表»,.«無覆無記»,.«第二靜慮»⟩, by decide⟩
theorem «撤染色屬業» : ∃ x : «色法», «無表有記» x ∧ «表業繫地» x ∧ «欲界無有覆表» x ∧ «有覆色異地反例» x := ⟨⟨.«其餘»,.«有覆無記»,.«欲界»⟩, by decide⟩
theorem «撤無表有記» : ∃ x : «色法», «染色屬業» x ∧ «表業繫地» x ∧ «欲界無有覆表» x ∧ «有覆色異地反例» x := ⟨⟨.«無表»,.«有覆無記»,.«欲界»⟩, by decide⟩
theorem «撤表業繫地» : ∃ x : «色法», «染色屬業» x ∧ «無表有記» x ∧ «欲界無有覆表» x ∧ «有覆色異地反例» x := ⟨⟨.«語表»,.«有覆無記»,.«第二靜慮»⟩, by decide⟩
theorem «撤欲界排除» : ∃ x : «色法», «染色屬業» x ∧ «無表有記» x ∧ «表業繫地» x ∧ «有覆色異地反例» x := ⟨⟨.«身表»,.«有覆無記»,.«欲界»⟩, by decide⟩
theorem «初定繫之逆不成» : ∃ x : «色法», «四規則皆成立» x ∧ x.«繫屬» = .«初靜慮» ∧ ¬ «有覆無記色» x :=
  ⟨⟨.«語表»,.«善»,.«初靜慮»⟩, by decide⟩
theorem «有覆色可存在» : ∃ x : «色法», «四規則皆成立» x ∧ «有覆無記色» x := ⟨⟨.«語表»,.«有覆無記»,.«初靜慮»⟩, by decide⟩
theorem «可無有覆色» : ∃ W : «色法» → Prop, (∃ x, W x) ∧ (∀ x, W x → «四規則皆成立» x) ∧
    ¬ ∃ x, W x ∧ «有覆無記色» x := by
  let s : «色法» := ⟨.«語表»,.«善»,.«欲界»⟩
  refine ⟨fun x => x = s, ⟨s,rfl⟩, ?_, ?_⟩
  · intro x h; subst x; decide
  · rintro ⟨x,h,n⟩; subst x; exact «四性».noConfusion n

/-- 文證一。得與所得法相聯，從關於得的文句讀出所得法的繫地。 -/
theorem «由得推所得法» {«得» : Type} («所得法» : «得» → «色法») (x : «色法»)
    (has : «有覆無記色» x → ∃ d, «所得法» d = x)
    (reading : ∀ d, «有覆無記色» («所得法» d) → («所得法» d).«繫屬» = .«初靜慮»)
    (c : «有覆無記色» x) : x.«繫屬» = .«初靜慮» := by
  obtain ⟨d,h⟩ := has c
  exact h ▸ reading d (h.symm ▸ c)
/-- 文證二。給有覆表的文句加上「有覆色屬表」這一中間結果。 -/
theorem «由表證色» (x : «色法») (k : «染色屬業» x) (a : «無表有記» x)
    (reading : «有覆無記色» x → «表色» x → x.«繫屬» = .«初靜慮») (c : «有覆無記色» x) : x.«繫屬» = .«初靜慮» :=
  reading c («有覆無記色是表» x k a c)

def «十二心列舉» : List «十二心» := [.«欲界善心»,.«欲界不善心»,.«欲界有覆心»,.«欲界無覆心»,.«色界善心»,.«色界有覆心»,
  .«色界無覆心»,.«無色界善心»,.«無色界有覆心»,.«無色界無覆心»,.«學心»,.«無學心»]
theorem «十二心窮盡» : «十二心列舉».Nodup ∧ ∀ c : «十二心», c ∈ «十二心列舉» := by
  constructor
  · decide
  · intro c; cases c <;> decide
/-- 各善心現前位容得心的聯集。欲善、欲無覆是兩個分開的開關。 -/
def «容得» («欲界善心» «欲界無覆心» : Bool) : «十二心» → Bool
  | .«色界善心» | .«色界無覆心» | .«無色界善心» | .«學心» | .«無學心» => true
  | .«欲界善心» => «欲界善心»
  | .«欲界無覆心» => «欲界無覆心»
  | _ => false
def «得心名單» (a b : Bool) := «十二心列舉».filter («容得» a b)
theorem «六七心計數» : («得心名單» false true).length = 6 ∧ («得心名單» true true).length = 7 ∧
    («得心名單» true false).length = 6 := by decide
theorem «六心名單之異» (m : «十二心») : «容得» false true m ≠ «容得» true false m ↔
    m = .«欲界善心» ∨ m = .«欲界無覆心» := by cases m <;> decide
theorem «七心之充要條件» (a b : Bool) : («得心名單» a b).length = 7 ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

abbrev «已斷品數» := «成就論».«已斷品數»
theorem «未全離容斷一品» : (1 : «已斷品數»).val < 9 ∧ (1 : «已斷品數»).val ≠ 0 := by decide
theorem «未全離容未斷一品» : (0 : «已斷品數»).val < 9 ∧ (0 : «已斷品數»).val = 0 := by decide
theorem «無斷道則無新斷品» (n : «已斷品數») («能斷道» : Prop) (needed : 0 < n.val → «能斷道»)
    (blocked : ¬ «能斷道») : n.val = 0 := Nat.eq_zero_of_not_pos (fun pos => blocked (needed pos))

end AbhiLib.«分別實驗»
