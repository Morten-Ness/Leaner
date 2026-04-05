import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem kronecker_ofNat [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : ℕ)
    [b.AtLeastTwo] : A ⊗ₖ (ofNat(b) : Matrix n n α) =
      blockDiagonal fun _ => A <• (ofNat(b) : α) := Matrix.kronecker_diagonal _ _

