import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem contsAux_recurrence {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.contsAux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  simp [*, contsAux, nextConts, nextDen, nextNum]

