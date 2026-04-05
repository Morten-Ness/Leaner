import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partDens.get? n = some gp.b := by simp [partDens, s_nth_eq]

