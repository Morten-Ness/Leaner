import Mathlib

variable {R M : Type*}

theorem infinite_range_add_nsmul_iff [AddCommGroup M] [IsAddTorsionFree M] (x y : M) :
    (Set.range <| fun n : ℕ ↦ x + n • y).Infinite ↔ y ≠ 0 := by
  refine ⟨fun h hy ↦ by simp [hy] at h, fun h ↦ Set.infinite_range_of_injective fun r s hrs ↦ ?_⟩
  rw [add_right_inj, ← natCast_zsmul, ← natCast_zsmul] at hrs
  simpa using smul_left_injective _ h hrs

