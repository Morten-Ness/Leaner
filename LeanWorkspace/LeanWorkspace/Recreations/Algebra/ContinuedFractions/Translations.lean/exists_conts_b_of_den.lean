import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem exists_conts_b_of_den {B : K} (nth_denom_eq : g.dens n = B) :
    ∃ conts, g.conts n = conts ∧ conts.b = B := by simpa

