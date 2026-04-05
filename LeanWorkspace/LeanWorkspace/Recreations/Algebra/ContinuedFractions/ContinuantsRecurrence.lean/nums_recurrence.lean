import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem nums_recurrence {gp : Pair K} {ppredA predA : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_num_eq : g.nums n = ppredA)
    (succ_nth_num_eq : g.nums (n + 1) = predA) :
    g.nums (n + 2) = gp.b * predA + gp.a * ppredA := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.conts n = conts ∧ conts.a = ppredA :=
    exists_conts_a_of_num nth_num_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      ∃ conts, g.conts (n + 1) = conts ∧ conts.a = predA :=
    exists_conts_a_of_num succ_nth_num_eq
  rw [num_eq_conts_a, GenContFract.conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

