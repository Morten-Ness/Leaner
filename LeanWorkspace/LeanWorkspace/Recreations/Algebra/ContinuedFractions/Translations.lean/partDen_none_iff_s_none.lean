import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem partDen_none_iff_s_none : g.partDens.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partDens, s_nth_eq]

