import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem smul_opposite_image_mul_preimage' (g : G) (h : Gᵐᵒᵖ) (s : Set G) :
    (fun y => h • y) '' ((g * ·) ⁻¹' s) = (g * ·) ⁻¹' ((fun y => h • y) '' s) := by
  simp [preimage_preimage, mul_assoc]

-- TODO: deprecate?

