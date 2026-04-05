import Mathlib

variable {α R S : Type*}

theorem map_multiset_prod [CommSemiring R] [CommSemiring S] (f : R ≃+* S)
    (s : Multiset R) : f s.prod = (s.map f).prod := map_multiset_prod f s

