import AbhiLib
open AbhiLib AbhiLib.Experiments

-- 若只知「是色」，缺少前提10的色業歸屬，第46步的推論就會失敗。
example : ∃ x : Rupa, x.form ≠ .unmanifest ∧ Covered x ∧ ¬ Manifest x :=
  ⟨⟨.other,.covered,.desire⟩, by decide⟩

-- 善表、不善表、無覆表都不會單憑「表」而自動取得有覆性。
example : ∃ x : Rupa, Valid x ∧ Manifest x ∧ ¬ Covered x :=
  ⟨⟨.body,.good,.desire⟩, by decide⟩

-- 初定有覆身表與語表各自滿足四條局部規則。
example : Valid ⟨.body,.covered,.first⟩ ∧ Valid ⟨.speech,.covered,.first⟩ := by decide

-- 把毘婆沙師的表業範圍換成有餘師，三定有覆語表依然被排除。
example (x : Rupa) (k : K x) (a : A x) (o : Other x) (d : D x) (h : x.ground = .third) :
    ¬ Covered x := fun c => Ground.noConfusion (h.symm.trans (otherFirst x k a o d c))

-- 有餘師放寬的是無覆表；不善表同樣不在放寬範圍內。
example : ¬ Other ⟨.speech,.bad,.third⟩ := by decide

-- 無表排除無記性，單獨就能推出無表不是無覆無記。
example (x : Rupa) (a : A x) (h : x.form = .unmanifest) : x.nature ≠ .clear :=
  fun n => a h (Or.inr n)

-- 得心計數排除欲善、欲無覆兩者時，只餘共同的五心。
example : (roster false false).length = 5 := by decide

-- 即使計數相等，欲善仍可辨別這兩種六心讀法。
example : allows false true .desireGood ≠ allows true false .desireGood := by decide

-- 上一例的差異沒有波及有學與無學。
example : allows false true .learner = allows true false .learner ∧
    allows false true .adept = allows true false .adept := by decide

-- 「未全斷」還容許已新斷八品的純數值模型。
example : (8 : Grades).val < 9 ∧ (8 : Grades).val ≠ 0 := by decide
