import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem Monic.natDegree_eq_zero (hf : p.Monic) : p.natDegree = 0 ↔ p = 1 := ⟨Polynomial.eq_one_of_monic_natDegree_zero hf, by rintro rfl; simp⟩

