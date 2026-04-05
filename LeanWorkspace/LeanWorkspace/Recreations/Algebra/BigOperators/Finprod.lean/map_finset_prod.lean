import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem map_finset_prod {α F : Type*} [Fintype α] [EquivLike F M N] [MulEquivClass F M N] (f : F)
    (g : α → M) : f (∏ i : α, g i) = ∏ i : α, f (g i) := by
  simp [← finprod_eq_prod_of_fintype, MulEquivClass.map_finprod]

