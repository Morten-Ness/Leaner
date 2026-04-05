import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem finset_prod_singleton {M ι : Type*} [CommMonoid M] (s : Finset ι) (I : ι → M) :
    ∏ i ∈ s, ({I i} : Set M) = {∏ i ∈ s, I i} := (map_prod (singletonMonoidHom : M →* Set M) _ _).symm

