import AbhiLib
import Lean
open Lean AbhiLib AbhiLib.«分別實驗»

def forms : List («色法種類» × String) := [(.«身表»,"身表"),(.«語表»,"語表"),(.«無表»,"無表"),(.«其餘»,"其餘色")]
def natures : List («四性» × String) := [(.«善»,"善"),(.«不善»,"不善"),(.«有覆無記»,"有覆無記"),(.«無覆無記»,"無覆無記")]
def grounds : List («繫不繫» × String) := [(.«欲界»,"欲界"),(.«初靜慮»,"初靜慮"),(.«第二靜慮»,"第二靜慮"),
  (.«第三靜慮»,"第三靜慮"),(.«第四靜慮»,"第四靜慮"),(.«無色界»,"無色界"),(.«不繫»,"不繫")]
theorem exhaustive : (forms.map Prod.fst).Nodup ∧ (natures.map Prod.fst).Nodup ∧
    (grounds.map Prod.fst).Nodup ∧ (∀ f : «色法種類», f ∈ forms.map Prod.fst) ∧
    (∀ n : «四性», n ∈ natures.map Prod.fst) ∧ (∀ g : «繫不繫», g ∈ grounds.map Prod.fst) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
  all_goals intro item; cases item <;> decide
def row (f : «色法種類» × String) (n : «四性» × String) (g : «繫不繫» × String) : Json :=
  let x : «色法» := ⟨f.1,n.1,g.1⟩
  Json.mkObj [("features", toJson [f.2,n.2,g.2]),
    ("rules",toJson [decide («染色屬業» x), decide («無表有記» x), decide («表業繫地» x), decide («欲界無有覆表» x), decide («有餘師表業繫地» x)]),
    ("counter",toJson (decide («有覆色異地反例» x)))]
def mindName : «十二心» → String
  | .«欲界善心» => "欲善" | .«欲界不善心» => "欲不善" | .«欲界有覆心» => "欲有覆" | .«欲界無覆心» => "欲無覆"
  | .«色界善心» => "色善" | .«色界有覆心» => "色有覆" | .«色界無覆心» => "色無覆"
  | .«無色界善心» => "無色善" | .«無色界有覆心» => "無色有覆" | .«無色界無覆心» => "無色無覆"
  | .«學心» => "有學" | .«無學心» => "無學"
def main : IO Unit := do
  let rows := forms.flatMap (fun f => natures.flatMap (fun n => grounds.map (row f n)))
  let reads := [(false,true),(true,true),(true,false)].map (fun (a,b) => («得心名單» a b).map mindName)
  IO.println (Json.mkObj [("rows", toJson rows), ("readings", toJson reads)]).compress
