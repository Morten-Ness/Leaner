import Mathlib

variable {α β R n m : Type*}

theorem isDiag_neg_iff [SubtractionMonoid α] {A : Matrix n n α} : (-A).IsDiag ↔ A.IsDiag := ⟨fun ha _ _ h => neg_eq_zero.1 (ha h), Matrix.IsDiag.neg⟩

