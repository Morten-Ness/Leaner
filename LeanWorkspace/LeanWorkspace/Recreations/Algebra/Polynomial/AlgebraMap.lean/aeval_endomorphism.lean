import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommRing R] {p : R[X]} {t : R}

theorem aeval_endomorphism {M : Type*} [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (v : M) (p : R[X]) : Polynomial.aeval f p v = p.sum fun n b => b • (f ^ n) v := by
  rw [Polynomial.aeval_def, eval₂_eq_sum]
  exact map_sum (LinearMap.applyₗ v) _ _

