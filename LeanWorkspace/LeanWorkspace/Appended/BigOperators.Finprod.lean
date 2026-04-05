import Mathlib

section

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

theorem hasFiniteMulSupport_fun_pow_count (s : Multiset α) (f : α → M) :
    (fun a ↦ (f a) ^ s.count a).HasFiniteMulSupport := s.toFinset.finite_toSet.subset <| Multiset.mulSupport_fun_pow_count_subset ..

end

section

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

theorem prod_map_eq_finprod (s : Multiset α) (f : α → M) :
    (s.map f).prod = ∏ᶠ a, f a ^ s.count a := by
  rw [Finset.prod_multiset_map_count, eq_comm]
  exact finprod_eq_prod_of_mulSupport_subset _ <| Multiset.mulSupport_fun_pow_count_subset ..

end
