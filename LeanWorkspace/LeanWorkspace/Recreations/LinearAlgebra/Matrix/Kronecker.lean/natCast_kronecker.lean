import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem natCast_kronecker [NonAssocSemiring α] [DecidableEq l] (a : ℕ) (B : Matrix m n α) :
    (a : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (blockDiagonal fun _ => a • B) := Matrix.diagonal_kronecker _ _ |>.trans <| by
    congr! 2
    ext
    simp [(Nat.cast_commute a _).eq]

