import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem image_finset_prod (f : F) (m : Finset ι) (s : ι → Set α) :
    ((f : α → β) '' ∏ i ∈ m, s i) = ∏ i ∈ m, f '' s i := (Set.image_multiset_prod f _).trans <| congr_arg Multiset.prod <| Multiset.map_map _ _ _

