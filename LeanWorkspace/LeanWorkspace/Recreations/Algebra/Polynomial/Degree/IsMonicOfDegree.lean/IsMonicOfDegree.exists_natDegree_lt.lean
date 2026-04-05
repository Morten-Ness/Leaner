import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.exists_natDegree_lt {p : R[X]} {n : ℕ} (hn : n ≠ 0)
    (hp : IsMonicOfDegree p n) :
    ∃ q : R[X], p = X ^ n + q ∧ q.natDegree < n := by
  refine ⟨p.eraseLead, ?_, ?_⟩
  · nth_rewrite 1 [← p.eraseLead_add_C_mul_X_pow]
    rw [add_comm, hp.natDegree_eq, hp.leadingCoeff_eq, map_one, one_mul]
  · refine p.eraseLead_natDegree_le.trans_lt ?_
    rw [hp.natDegree_eq]
    lia

