import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem natCast_kronecker_natCast [NonAssocSemiring α] [DecidableEq m] [DecidableEq n] (a b : ℕ) :
    (a : Matrix m m α) ⊗ₖ (b : Matrix n n α) = ↑(a * b) := (Matrix.diagonal_kronecker_diagonal _ _).trans <| by simp_rw [← Nat.cast_mul]; rfl

