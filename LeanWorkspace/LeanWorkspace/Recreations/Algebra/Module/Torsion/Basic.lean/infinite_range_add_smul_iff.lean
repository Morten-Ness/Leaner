import Mathlib

variable {R M : Type*}

theorem infinite_range_add_smul_iff [Ring R] [IsDomain R] [Infinite R] [AddCommGroup M] [Module R M]
    [IsTorsionFree R M] (x y : M) :
    (Set.range <| fun r : R ↦ x + r • y).Infinite ↔ y ≠ 0 := by
  refine ⟨fun h hy ↦ by simp [hy] at h, fun h ↦ Set.infinite_range_of_injective fun r s hrs ↦ ?_⟩
  rw [add_right_inj] at hrs
  exact smul_left_injective _ h hrs

