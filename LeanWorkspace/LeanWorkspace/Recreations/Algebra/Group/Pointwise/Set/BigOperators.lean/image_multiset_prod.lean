import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem image_multiset_prod (f : F) :
    ∀ m : Multiset (Set α), (f : α → β) '' m.prod = (m.map fun s => f '' s).prod := Quotient.ind <| by
    simpa only [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe] using
      Set.image_list_prod f

