import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem list_prod_singleton {M : Type*} [Monoid M] (s : List M) :
    (s.map fun i ↦ ({i} : Set M)).prod = {s.prod} := (map_list_prod (singletonMonoidHom : M →* Set M) _).symm

