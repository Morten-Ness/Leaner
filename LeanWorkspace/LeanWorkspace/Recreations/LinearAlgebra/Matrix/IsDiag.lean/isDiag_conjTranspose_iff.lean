import Mathlib

variable {α β R n m : Type*}

theorem isDiag_conjTranspose_iff [NonUnitalNonAssocSemiring α] [StarRing α] {A : Matrix n n α} :
    Aᴴ.IsDiag ↔ A.IsDiag := ⟨fun ha => by
    convert ha.conjTranspose
    simp, Matrix.IsDiag.conjTranspose⟩

