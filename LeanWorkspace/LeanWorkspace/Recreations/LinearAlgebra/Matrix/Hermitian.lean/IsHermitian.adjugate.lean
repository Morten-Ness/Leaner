import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [CommRing α] [StarRing α]

theorem IsHermitian.adjugate [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A.adjugate.IsHermitian := by simp [Matrix.IsHermitian, adjugate_conjTranspose, hA.eq]

