import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem first_cont_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.conts 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [GenContFract.nth_cont_eq_succ_nth_contAux, GenContFract.second_contAux_eq zeroth_s_eq]

