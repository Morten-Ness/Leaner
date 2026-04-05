import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem first_den_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.dens 1 = gp.b := by simp [GenContFract.den_eq_conts_b, GenContFract.first_cont_eq zeroth_s_eq]

