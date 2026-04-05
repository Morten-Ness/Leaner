import Mathlib

variable {α β n m R : Type*}

theorem isSymm_comp_iff_forall {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsSymm ↔ ∀ i j i' j', A j i j' i' = A i j i' j' := by
  simp [Matrix.IsSymm.ext_iff]
  grind

