import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem partNum_none_iff_s_none : g.partNums.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partNums, s_nth_eq]

