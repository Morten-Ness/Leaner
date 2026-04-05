import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partNums.get? n = some gp.a := by simp [partNums, s_nth_eq]

