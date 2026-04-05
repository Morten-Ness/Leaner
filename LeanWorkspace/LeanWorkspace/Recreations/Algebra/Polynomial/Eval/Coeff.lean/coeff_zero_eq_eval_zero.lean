import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem coeff_zero_eq_eval_zero (p : R[X]) : coeff p 0 = p.eval 0 := calc
    coeff p 0 = coeff p 0 * 0 ^ 0 := by simp
    _ = p.eval 0 := by
      symm
      rw [eval_eq_sum]
      exact Finset.sum_eq_single _ (fun b _ hb => by simp [zero_pow hb]) (by simp)

