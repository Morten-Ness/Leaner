import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem degree_derivative_eq [IsAddTorsionFree R] (p : R[X]) (hp : 0 < natDegree p) :
    degree (Polynomial.derivative p) = (natDegree p - 1 : ℕ) := by
  apply le_antisymm
  · rw [Polynomial.derivative_apply]
    apply le_trans (degree_sum_le _ _) (Finset.sup_le _)
    intro n hn
    apply le_trans (degree_C_mul_X_pow_le _ _) (WithBot.coe_le_coe.2 (tsub_le_tsub_right _ _))
    apply le_natDegree_of_mem_supp _ hn
  · refine le_sup ?_
    rw [Polynomial.mem_support_derivative, tsub_add_cancel_of_le, mem_support_iff]
    · rw [coeff_natDegree, Ne, leadingCoeff_eq_zero]
      intro h
      rw [h, natDegree_zero] at hp
      exact hp.false
    exact hp

