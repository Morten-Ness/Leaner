import Mathlib

variable {α β n m R : Type*}

theorem isSymm_map_iff {A : Matrix n n α} {f : α → β} (hf : f.Injective) :
    (A.map f).IsSymm ↔ A.IsSymm := by
  rw [Matrix.IsSymm, Matrix.IsSymm, ← transpose_map, map_injective hf |>.eq_iff]

