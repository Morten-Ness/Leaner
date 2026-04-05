import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem IsHermitian.of_subsingleton {A : Matrix n n α} [Subsingleton α] : A.IsHermitian := .ext fun _ _ ↦ Subsingleton.elim ..

