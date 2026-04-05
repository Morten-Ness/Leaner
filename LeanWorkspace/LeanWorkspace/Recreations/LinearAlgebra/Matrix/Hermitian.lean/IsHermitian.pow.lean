import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Semiring α] [StarRing α]

theorem IsHermitian.pow [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsHermitian) (k : ℕ) :
    (A ^ k).IsHermitian := IsSelfAdjoint.pow h _

