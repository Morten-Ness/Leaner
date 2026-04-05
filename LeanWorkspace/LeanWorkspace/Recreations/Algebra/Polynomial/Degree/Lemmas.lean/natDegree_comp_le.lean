import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_comp_le : natDegree (p.comp q) ≤ natDegree p * natDegree q := letI := Classical.decEq R
  if h0 : p.comp q = 0 then by rw [h0, natDegree_zero]; exact Nat.zero_le _
  else
    WithBot.coe_le_coe.1 <|
      calc
        ↑(natDegree (p.comp q)) = degree (p.comp q) := (degree_eq_natDegree h0).symm
        _ = _ := congr_arg degree comp_eq_sum_left
        _ ≤ _ := degree_sum_le _ _
        _ ≤ _ :=
          Finset.sup_le fun n hn =>
            calc
              degree (Polynomial.C (coeff p n) * q ^ n) ≤ degree (Polynomial.C (coeff p n)) + degree (q ^ n) :=
                degree_mul_le _ _
              _ ≤ natDegree (Polynomial.C (coeff p n)) + n • degree q :=
                (add_le_add Polynomial.degree_le_natDegree (degree_pow_le _ _))
              _ ≤ natDegree (Polynomial.C (coeff p n)) + n • ↑(natDegree q) := by grw [Polynomial.degree_le_natDegree]
              _ = (n * natDegree q : ℕ) := by
                rw [natDegree_C, Nat.cast_zero, zero_add, nsmul_eq_mul]
                simp
              _ ≤ (natDegree p * natDegree q : ℕ) :=
                WithBot.coe_le_coe.2 <|
                  mul_le_mul_of_nonneg_right (le_natDegree_of_ne_zero (mem_support_iff.1 hn))
                    (Nat.zero_le _)

