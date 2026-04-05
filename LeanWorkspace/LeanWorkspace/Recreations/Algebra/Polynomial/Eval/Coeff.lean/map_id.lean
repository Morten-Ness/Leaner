import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_id : p.map (RingHom.id _) = p := by simp [Polynomial.ext_iff, Polynomial.coeff_map]

