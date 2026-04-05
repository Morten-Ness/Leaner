import Mathlib

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

theorem mulSupport_fun_pow_count_subset (s : Multiset α) (f : α → M) :
    (fun a ↦ f a ^ count a s).mulSupport ⊆ s.toFinset := by
  simp +contextual [not_imp_comm]

