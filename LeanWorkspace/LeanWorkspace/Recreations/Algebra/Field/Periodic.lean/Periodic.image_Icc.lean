import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.image_Icc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Icc a (a + c) = Set.range f := (image_subset_range _ _).antisymm <| h.image_Ioc hc a ▸ image_mono Ioc_subset_Icc_self

