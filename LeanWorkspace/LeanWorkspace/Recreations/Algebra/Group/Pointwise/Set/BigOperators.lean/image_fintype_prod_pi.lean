import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem image_fintype_prod_pi [Fintype ι] (S : ι → Set α) :
    (fun f : ι → α => ∏ i, f i) '' univ.pi S = ∏ i, S i := by
  simpa only [Finset.coe_univ] using Set.image_finset_prod_pi Finset.univ S

