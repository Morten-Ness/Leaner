import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem second_contAux_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.contsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [zeroth_s_eq, contsAux, nextConts, nextDen, nextNum]

