import AbhiLib.«分類»

namespace AbhiLib.«成就論»

inductive «沙門果» where
  | «預流果» | «一來果» | «不還果» | «阿羅漢果»
  deriving DecidableEq

/-- 記當下已得的最高果；未得初果的聖者另列。 -/
inductive «位次» where
  | «異生» | «預流向» | «持果» («果» : «沙門果»)
  deriving DecidableEq

def «聖者» (s : «位次») : Prop := s ≠ .«異生»

/-- 生地的九種取值。無漏法的「不繫」不能作為有情的出生地。 -/
inductive «生地九地» where
  | «欲界» | «初靜慮» | «第二靜慮» | «第三靜慮» | «第四靜慮»
  | «空無邊處» | «識無邊處» | «無所有處» | «非想非非想處»
  deriving DecidableEq

abbrev «已斷品數» := Fin 10
inductive «等至種類» where | «味相應» | «淨» | «無漏» deriving DecidableEq

/-- 根本靜慮的成就取決於此人當時的狀態。 -/
structure «人位» where
  «所居位» : «位次»
  «生地» : «生地九地»
  «諸地已斷品數» : «生地九地» → «已斷品數»
  «成就» : «根本靜慮» → «等至種類» → Prop

def «已離染» (p : «人位») (g : «生地九地») : Prop := p.«諸地已斷品數» g = 9

def «成就根本靜慮» (p : «人位») (l : «根本靜慮») : Prop := ∃ k, p.«成就» l k

def «欲界或梵世» (b : «生地九地») : Prop := b = .«欲界» ∨ b = .«初靜慮»

theorem «持果者是聖者» {p : «人位»} {f : «沙門果»} (h : p.«所居位» = .«持果» f) :
    «聖者» p.«所居位» := by rw [h]; exact «位次».noConfusion

end AbhiLib.«成就論»
