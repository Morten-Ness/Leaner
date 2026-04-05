import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_map {S : Type*} [CommSemiring S] (f : R →+* S) (p : R[X]) (n : ℕ) :
    Polynomial.homogenize (p.map f) n = MvPolynomial.map f (Polynomial.homogenize p n) := by
  simp [Polynomial.homogenize]

