import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem _root_.Associated.roots_eq {p q : R[X]} (h : Associated p q) : p.roots = q.roots := by
  obtain ⟨u, rfl⟩ := h
  rw [eq_C_of_degree_eq_zero <| degree_coe_units u, mul_comm,
    Polynomial.roots_C_mul _ <| coeff_coe_units_zero_ne_zero u]

