import Mathlib

variable {F α β γ : Type*}

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (m : F) {s t : Set α}

theorem preimage_div (hm : Function.Injective m) {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) :
    m ⁻¹' (s / t) = m ⁻¹' s / m ⁻¹' t := hm.image_injective <| by
    rw [Set.image_div, image_preimage_eq_iff.2 hs, image_preimage_eq_iff.2 ht,
      image_preimage_eq_iff.2 (Set.div_subset_range m hs ht)]

