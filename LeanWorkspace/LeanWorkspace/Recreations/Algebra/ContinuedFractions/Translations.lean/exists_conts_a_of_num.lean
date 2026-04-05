import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem exists_conts_a_of_num {A : K} (nth_num_eq : g.nums n = A) :
    ∃ conts, g.conts n = conts ∧ conts.a = A := by simpa

