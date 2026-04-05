import Mathlib

variable {R : Type*}

variable [CommRing R]

theorem IsMonicOfDegree.aeval_sub {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X - C r) p) n := by
  rw [sub_eq_add_neg, ← map_neg]
  exact aeval_add hp (-r)

