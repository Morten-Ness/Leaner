import Mathlib

variable {R : Type*}

variable [CommSemiring R] {a b : {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1}}

theorem mul_eq_zero_add_eq_one_ext_right (eq : a.1.2 = b.1.2) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq_of_mul_eq_add_eq_one a.1.2 ?_ ?_ ?_, eq⟩
  · rw [mul_comm, a.2.1, eq, b.2.1]
  · rw [add_comm, a.2.2]
  · rw [add_comm, eq, b.2.2]

