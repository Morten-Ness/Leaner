import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem ofFn_comp_toFn_eq_id_of_natDegree_lt {n : ℕ} {p : R[X]} (h_deg : p.natDegree < n) :
    Polynomial.ofFn n (Polynomial.toFn n p) = p := by
  ext i
  by_cases! h : i < n
  · simp [h, Polynomial.toFn]
  · have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt <| by lia
    simp [*]

