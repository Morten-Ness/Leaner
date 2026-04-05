import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem isHermitian_map_iff {A : Matrix n n α} {f : α → β} (hf : Function.Semiconj f star star)
    (hinj : f.Injective) : (A.map f).IsHermitian ↔ A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.IsHermitian, ← conjTranspose_map f hf, map_injective hinj |>.eq_iff]

