import Mathlib

open scoped Polynomial

variable {K : Type*} [Field K] (R : Subring K)

variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)

variable {L : Type*} [Field L] [Algebra K L]

theorem int_eval₂_eq (x : L) :
    eval₂ (algebraMap R L) x (P.int R hP) = aeval x P := by
  rw [aeval_eq_sum_range, eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)

