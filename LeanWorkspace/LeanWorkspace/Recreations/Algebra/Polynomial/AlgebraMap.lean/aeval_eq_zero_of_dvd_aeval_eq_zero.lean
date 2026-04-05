import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_eq_zero_of_dvd_aeval_eq_zero [CommSemiring S] [CommSemiring T] [Algebra S T]
    {p q : S[X]} (h₁ : p ∣ q) {a : T} (h₂ : Polynomial.aeval a p = 0) : Polynomial.aeval a q = 0 := by
  rw [← Polynomial.eval_map_algebraMap] at h₂ ⊢
  exact eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd (algebraMap S T) h₁) h₂

