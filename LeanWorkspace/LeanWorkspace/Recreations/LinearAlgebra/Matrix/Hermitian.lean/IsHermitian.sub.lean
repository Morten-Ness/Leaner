import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddGroup α] [StarAddMonoid α]

theorem IsHermitian.sub {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A - B).IsHermitian := IsSelfAdjoint.sub hA hB

