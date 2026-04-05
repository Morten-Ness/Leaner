import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_add (p q : R[X]) (n : ℕ) :
    Polynomial.homogenize (p + q) n = Polynomial.homogenize p n + Polynomial.homogenize q n := by
  simp [Polynomial.homogenize, Finset.sum_add_distrib]

