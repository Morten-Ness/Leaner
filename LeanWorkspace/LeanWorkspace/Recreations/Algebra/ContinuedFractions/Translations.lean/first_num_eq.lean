import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem first_num_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by simp [GenContFract.num_eq_conts_a, GenContFract.first_cont_eq zeroth_s_eq]

