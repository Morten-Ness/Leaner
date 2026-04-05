import Mathlib

variable {R : Type*}

variable [CommSemiring R] {a b : {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1}}

theorem mul_eq_zero_add_eq_one_ext_left (eq : a.1.1 = b.1.1) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq, eq_of_mul_eq_add_eq_one a.1.1 ?_ a.2.2 ?_⟩
  · rw [a.2.1, mul_comm, eq, b.2.1]
  · rw [eq, b.2.2]

