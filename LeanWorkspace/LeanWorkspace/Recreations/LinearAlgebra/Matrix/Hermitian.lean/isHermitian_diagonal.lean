import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddMonoid α] [StarAddMonoid α]

theorem isHermitian_diagonal [TrivialStar α] [DecidableEq n] (v : n → α) :
    (diagonal v).IsHermitian := Matrix.isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)

