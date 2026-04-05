import Mathlib

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

theorem hasFiniteMulSupport_fun_pow_count (s : Multiset α) (f : α → M) :
    (fun a ↦ (f a) ^ s.count a).HasFiniteMulSupport := s.toFinset.finite_toSet.subset <| Multiset.mulSupport_fun_pow_count_subset ..

