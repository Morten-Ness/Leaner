import Mathlib

variable {α β n m R : Type*}

theorem isSymm_conjTranspose_iff [InvolutiveStar α] {A : Matrix n n α} : Aᴴ.IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.conjTranspose)⟩
  rw [← A.conjTranspose_conjTranspose]
  exact h.conjTranspose

