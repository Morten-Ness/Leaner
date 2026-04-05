import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [DivisionRing R] {p q : R[X]}

theorem degree_pos_of_ne_zero_of_nonunit (hp0 : p ≠ 0) (hp : ¬IsUnit p) : 0 < degree p := lt_of_not_ge fun h => by
    rw [eq_C_of_degree_le_zero h] at hp0 hp
    exact hp (IsUnit.map Polynomial.C (IsUnit.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))))

