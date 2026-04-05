import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem induction_with_natDegree_le (motive : R[X] → Prop) (N : ℕ) (zero : motive 0)
    (C_mul_pow : ∀ n : ℕ, ∀ r : R, r ≠ 0 → n ≤ N → motive (Polynomial.C r * Polynomial.X ^ n))
    (add : ∀ f g : R[X], f.natDegree < g.natDegree → g.natDegree ≤ N →
      motive f → motive g → motive (f + g)) (f : R[X]) (df : f.natDegree ≤ N) : motive f := by
  induction hf : #f.support generalizing f with
  | zero =>
    convert zero
    simpa [support_eq_empty, card_eq_zero] using hf
  | succ c hc =>
    rw [← Polynomial.eraseLead_add_C_mul_X_pow f]
    cases c
    · convert C_mul_pow f.natDegree f.leadingCoeff ?_ df using 1
      · convert zero_add (Polynomial.C (leadingCoeff f) * Polynomial.X ^ f.natDegree)
        rw [← card_support_eq_zero, Polynomial.card_support_eraseLead' hf]
      · rw [leadingCoeff_ne_zero, Ne, ← card_support_eq_zero, hf]
        exact zero_ne_one.symm
    refine add f.eraseLead _ ?_ ?_ ?_ ?_
    · refine (Polynomial.eraseLead_natDegree_lt ?_).trans_le (le_of_eq ?_)
      · exact (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))).trans hf.ge
      · rw [natDegree_C_mul_X_pow _ _ (leadingCoeff_ne_zero.mpr _)]
        rintro rfl
        simp at hf
    · exact (natDegree_C_mul_X_pow_le f.leadingCoeff f.natDegree).trans df
    · exact hc _ (Polynomial.eraseLead_natDegree_le_aux.trans df) (Polynomial.card_support_eraseLead' hf)
    · refine C_mul_pow _ _ ?_ df
      rw [Ne, leadingCoeff_eq_zero, ← card_support_eq_zero, hf]
      exact Nat.succ_ne_zero _

