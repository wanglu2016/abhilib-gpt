import AbhiLib.Core

-- Preserve the public name used by the original twelve-mind experiments.
namespace AbhiLib.Experiments
inductive Mind12 where
  | desireGood | desireBad | desireCovered | desireClear | formGood | formCovered | formClear
  | formlessGood | formlessCovered | formlessClear | learner | adept deriving DecidableEq
end AbhiLib.Experiments

namespace AbhiLib.MindClasses
open Experiments (Mind12)

/-- 四性與十二心的對照。《俱舍論》卷七。 -/
def nature : Mind12 → Nature
  | .desireBad => .bad
  | .desireCovered | .formCovered | .formlessCovered => .covered
  | .desireClear | .formClear | .formlessClear => .clear
  | .desireGood | .formGood | .formlessGood | .learner | .adept => .good

def withOutflow : Mind12 → Bool
  | .learner | .adept => false
  | _ => true

theorem neutralWithOutflow (m : Mind12) (h : Neutral (nature m)) : withOutflow m := by
  cases m <;> simp_all [nature, Neutral, withOutflow]

end AbhiLib.MindClasses
