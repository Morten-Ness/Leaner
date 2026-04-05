import Mathlib

variable {ι κ M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R]

theorem list_sum_right (a : R) (l : List R) (h : ∀ b ∈ l, Commute a b) : Commute a l.sum := by
  induction l with
  | nil => exact Commute.zero_right _
  | cons x xs ih =>
    rw [List.sum_cons]
    exact (h _ mem_cons_self).add_right (ih fun j hj ↦ h _ <| mem_cons_of_mem _ hj)

