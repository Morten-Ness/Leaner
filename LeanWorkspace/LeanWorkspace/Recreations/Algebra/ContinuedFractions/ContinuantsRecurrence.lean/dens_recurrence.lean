import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem dens_recurrence {gp : Pair K} {ppredB predB : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_den_eq : g.dens n = ppredB)
    (succ_nth_den_eq : g.dens (n + 1) = predB) :
    g.dens (n + 2) = gp.b * predB + gp.a * ppredB := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.conts n = conts ∧ conts.b = ppredB :=
    exists_conts_b_of_den nth_den_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      ∃ conts, g.conts (n + 1) = conts ∧ conts.b = predB :=
    exists_conts_b_of_den succ_nth_den_eq
  rw [den_eq_conts_b, GenContFract.conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

