import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [NonUnitalSemiring α] [StarRing α]

theorem IsHermitian.commute_iff [Fintype n] {A B : Matrix n n α}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : Commute A B ↔ (A * B).IsHermitian := hA.isSelfAdjoint.commute_iff hB.isSelfAdjoint

