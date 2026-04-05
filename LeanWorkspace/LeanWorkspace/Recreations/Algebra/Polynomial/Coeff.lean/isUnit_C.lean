import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem isUnit_C {x : R} : IsUnit (Polynomial.C x) ↔ IsUnit x := ⟨fun h => (congr_arg IsUnit coeff_C_zero).mp (h.map <| @Polynomial.constantCoeff R _), fun h => h.map Polynomial.C⟩

