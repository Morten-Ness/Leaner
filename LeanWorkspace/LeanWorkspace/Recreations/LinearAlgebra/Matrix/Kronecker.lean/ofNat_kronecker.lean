import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem ofNat_kronecker [NonAssocSemiring α] [DecidableEq l] (a : ℕ) [a.AtLeastTwo]
    (B : Matrix m n α) : (ofNat(a) : Matrix l l α) ⊗ₖ B =
      Matrix.reindex (.prodComm _ _) (.prodComm _ _)
        (blockDiagonal fun _ => (ofNat(a) : α) • B) := Matrix.diagonal_kronecker _ _

