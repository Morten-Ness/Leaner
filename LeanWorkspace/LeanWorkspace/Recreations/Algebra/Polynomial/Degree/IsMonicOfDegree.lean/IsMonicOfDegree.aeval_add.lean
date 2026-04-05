import Mathlib

variable {R : Type*}

variable [CommRing R]

theorem IsMonicOfDegree.aeval_add {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X + C r) p) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  rw [← mul_one n]
  exact hp.comp one_ne_zero (Polynomial.isMonicOfDegree_X_add_one r)

