import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem smul_opposite_image_mul_preimage {H : Subgroup G} (g : G) (h : H.op) (s : Set G) :
    (fun y => h • y) '' ((g * ·) ⁻¹' s) = (g * ·) ⁻¹' ((fun y => h • y) '' s) := Subgroup.smul_opposite_image_mul_preimage' g h s

