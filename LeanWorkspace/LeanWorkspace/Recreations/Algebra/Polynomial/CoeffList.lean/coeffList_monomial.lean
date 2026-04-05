import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem coeffList_monomial {x : R} (hx : x ≠ 0) (n : ℕ) :
    (monomial n x).coeffList = x :: List.replicate n 0 := by
  have h := mt (Polynomial.monomial_eq_zero_iff x n).mp hx
  apply List.ext_get (by classical simp [hx])
  rintro (_ | k) _ h₁
  · exact (Polynomial.coeffList_eq_cons_leadingCoeff h).rec (by simp_all)
  · rw [List.length_cons, List.length_replicate] at h₁
    have : ((monomial n) x).natDegree.succ = n + 1 := by
      simp [Polynomial.natDegree_monomial_eq n hx]
    simpa [Polynomial.coeffList, withBotSucc_degree_eq_natDegree_add_one h]
      using Polynomial.coeff_monomial_of_ne _ (by lia)

