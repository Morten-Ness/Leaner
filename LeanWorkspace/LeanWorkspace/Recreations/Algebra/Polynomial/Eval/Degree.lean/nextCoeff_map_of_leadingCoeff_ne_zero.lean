import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] {f : R →+* S} {p : R[X]}

theorem nextCoeff_map_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f p.leadingCoeff ≠ 0) :
    (p.map f).nextCoeff = f p.nextCoeff := by
  grind [nextCoeff, Polynomial.natDegree_map_of_leadingCoeff_ne_zero, coeff_map]

