import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem isHermitian_comp_iff_forall {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsHermitian ↔ ∀ i j i' j', star (A j i j' i') = A i j i' j' := by
  simp [Matrix.IsHermitian.ext_iff]
  grind

