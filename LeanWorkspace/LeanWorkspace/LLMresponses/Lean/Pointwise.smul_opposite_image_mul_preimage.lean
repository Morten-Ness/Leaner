FAIL
import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem smul_opposite_image_mul_preimage {H : Subgroup G} (g : G) (h : H.op) (s : Set G) :
    (fun y => h • y) '' ((g * ·) ⁻¹' s) = (g * ·) ⁻¹' ((fun y => h • y) '' s) := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g * y, hy, ?_⟩
    rw [op_smul_eq_mul, mul_assoc]
  · rintro ⟨z, hz, hx⟩
    refine ⟨g⁻¹ * z, ?_, ?_⟩
    · simpa [hx, op_smul_eq_mul, mul_assoc] using hz
    · simp [hx, op_smul_eq_mul, mul_assoc]
