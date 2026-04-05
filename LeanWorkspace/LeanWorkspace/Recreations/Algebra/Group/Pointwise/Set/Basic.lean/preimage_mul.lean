import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β] (m : F) {s t : Set α}

theorem preimage_mul (hm : Function.Injective m) {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) :
    m ⁻¹' (s * t) = m ⁻¹' s * m ⁻¹' t := hm.image_injective <| by
    rw [Set.image_mul, image_preimage_eq_iff.2 hs, image_preimage_eq_iff.2 ht,
      image_preimage_eq_iff.2 (Set.mul_subset_range m hs ht)]

