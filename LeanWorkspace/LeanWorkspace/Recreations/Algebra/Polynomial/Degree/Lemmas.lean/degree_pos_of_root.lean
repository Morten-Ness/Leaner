import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_pos_of_root {p : R[X]} (hp : p ≠ 0) (h : IsRoot p a) : 0 < degree p := lt_of_not_ge fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [IsRoot, this, eval_C] at h
    simp only [h, map_zero] at this
    exact hp this

