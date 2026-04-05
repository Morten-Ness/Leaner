import Mathlib

variable {α β n m R : Type*}

theorem isSymm_comp_iff {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsSymm ↔ Aᵀ = A.map (·ᵀ) := by
  rw [Matrix.IsSymm, transpose_comp, transpose_map, comp .. |>.injective.eq_iff, eq_comm,
    transpose_involutive _ _ |>.eq_iff]

