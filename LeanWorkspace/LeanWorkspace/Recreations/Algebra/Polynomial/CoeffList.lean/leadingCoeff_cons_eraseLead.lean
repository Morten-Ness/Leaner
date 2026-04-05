import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem leadingCoeff_cons_eraseLead (h : P.nextCoeff ≠ 0) :
    P.leadingCoeff :: P.eraseLead.coeffList = P.coeffList := by
  have h₂ := ne_zero_of_natDegree_gt (natDegree_pos_of_nextCoeff_ne_zero h)
  have h₃ := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h
  simpa [natDegree_eraseLead_add_one h, Polynomial.coeffList, withBotSucc_degree_eq_natDegree_add_one h₂,
    withBotSucc_degree_eq_natDegree_add_one h₃, List.range_succ] using
    (Polynomial.eraseLead_coeff_of_ne · ·.ne)

