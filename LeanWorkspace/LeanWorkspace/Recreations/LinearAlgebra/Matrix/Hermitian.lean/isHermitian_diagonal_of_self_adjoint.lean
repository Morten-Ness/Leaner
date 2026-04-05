import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddMonoid α] [StarAddMonoid α]

theorem isHermitian_diagonal_of_self_adjoint [DecidableEq n] (v : n → α) (h : IsSelfAdjoint v) :
    (diagonal v).IsHermitian := (-- TODO: add a `pi.has_trivial_star` instance and remove the `funext`
        diagonal_conjTranspose v).trans <| congr_arg _ h

