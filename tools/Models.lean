import AbhiLib
import Lean
open Lean AbhiLib AbhiLib.Experiments

def forms : List (Form × String) := [(.body,"身表"),(.speech,"語表"),(.unmanifest,"無表"),(.other,"其餘色")]
def natures : List (Nature × String) := [(.good,"善"),(.bad,"不善"),(.covered,"有覆無記"),(.clear,"無覆無記")]
def grounds : List (Ground × String) := [(.desire,"欲界"),(.first,"初靜慮"),(.second,"第二靜慮"),
  (.third,"第三靜慮"),(.fourth,"第四靜慮"),(.formless,"無色界"),(.unbound,"不繫")]
theorem exhaustive : (forms.map Prod.fst).Nodup ∧ (natures.map Prod.fst).Nodup ∧
    (grounds.map Prod.fst).Nodup ∧ (∀ f : Form, f ∈ forms.map Prod.fst) ∧
    (∀ n : Nature, n ∈ natures.map Prod.fst) ∧ (∀ g : Ground, g ∈ grounds.map Prod.fst) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
  all_goals intro item; cases item <;> decide
def row (f : Form × String) (n : Nature × String) (g : Ground × String) : Json :=
  let x : Rupa := ⟨f.1,n.1,g.1⟩
  Json.mkObj [("features", toJson [f.2,n.2,g.2]),
    ("rules",toJson [decide (K x), decide (A x), decide (G x), decide (D x), decide (Other x)]),
    ("counter",toJson (decide (Counter x)))]
def mindName : Mind12 → String
  | .desireGood => "欲善" | .desireBad => "欲不善" | .desireCovered => "欲有覆" | .desireClear => "欲無覆"
  | .formGood => "色善" | .formCovered => "色有覆" | .formClear => "色無覆"
  | .formlessGood => "無色善" | .formlessCovered => "無色有覆" | .formlessClear => "無色無覆"
  | .learner => "有學" | .adept => "無學"
def main : IO Unit := do
  let rows := forms.flatMap (fun f => natures.flatMap (fun n => grounds.map (row f n)))
  let reads := [(false,true),(true,true),(true,false)].map (fun (a,b) => (roster a b).map mindName)
  IO.println (Json.mkObj [("rows", toJson rows), ("readings", toJson reads)]).compress
