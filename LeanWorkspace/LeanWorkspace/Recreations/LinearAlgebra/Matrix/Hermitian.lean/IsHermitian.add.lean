import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddMonoid α] [StarAddMonoid α]

theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian := IsSelfAdjoint.add hA hB

