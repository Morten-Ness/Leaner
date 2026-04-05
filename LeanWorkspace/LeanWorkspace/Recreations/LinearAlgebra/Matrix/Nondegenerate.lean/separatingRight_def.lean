import Mathlib

variable {m n R A : Type*} [CommRing R] [Fintype m] [Fintype n] [CommRing A] [IsDomain A]
  {M : Matrix m n R}

theorem separatingRight_def : M.SeparatingRight ↔ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  refine forall_congr' fun w ↦ ⟨fun hM hw ↦ hM ?_, fun hM hw ↦ hM ?_⟩ <;>
  convert hw

