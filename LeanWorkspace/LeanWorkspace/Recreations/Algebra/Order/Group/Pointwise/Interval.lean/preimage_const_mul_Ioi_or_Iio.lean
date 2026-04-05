import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_const_mul_Ioi_or_Iio (hb : a ≠ 0) {U V : Set α}
    (hU : U ∈ {s | ∃ a, s = Ioi a ∨ s = Iio a}) (hV : V = (a * ·) ⁻¹' U) :
    V ∈ {s | ∃ a, s = Ioi a ∨ s = Iio a} := by
  obtain ⟨aU, (haU | haU)⟩ := hU <;>
  simp only [hV, haU, mem_setOf_eq] <;>
  use a⁻¹ * aU <;>
  rcases lt_or_gt_of_ne hb with (hb | hb)
  · right; rw [Set.preimage_const_mul_Ioi_of_neg _ hb, div_eq_inv_mul]
  · left; rw [Set.preimage_const_mul_Ioi₀ _ hb, div_eq_inv_mul]
  · left; rw [Set.preimage_const_mul_Iio_of_neg _ hb, div_eq_inv_mul]
  · right; rw [Set.preimage_const_mul_Iio₀ _ hb, div_eq_inv_mul]

