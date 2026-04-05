import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [InvolutiveStar α]

theorem isHermitian_conjTranspose_iff {A : Matrix n n α} : Aᴴ.IsHermitian ↔ A.IsHermitian := IsSelfAdjoint.star_iff

