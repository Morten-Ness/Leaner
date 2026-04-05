import Mathlib

variable {R : Type*} [CommSemiring R]

theorem aeval_homogenize_of_eq_one {A : Type*} [CommSemiring A] [Algebra R A] {p : R[X]} {n : ℕ}
    (hn : natDegree p ≤ n) (g : Fin 2 → A) (hg : g 1 = 1) :
    MvPolynomial.aeval g (p.homogenize n) = aeval (g 0) p := by
  apply Polynomial.eval₂_homogenize_of_eq_one <;> assumption

