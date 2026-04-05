import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem multiset_prod_singleton {M : Type*} [CommMonoid M] (s : Multiset M) :
    (s.map fun i ↦ ({i} : Set M)).prod = {s.prod} := (map_multiset_prod (singletonMonoidHom : M →* Set M) _).symm

