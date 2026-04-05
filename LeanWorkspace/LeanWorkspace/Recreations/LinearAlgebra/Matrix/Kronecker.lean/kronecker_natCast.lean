import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem kronecker_natCast [NonAssocSemiring α] [DecidableEq n] (A : Matrix l m α) (b : ℕ) :
    A ⊗ₖ (b : Matrix n n α) = blockDiagonal fun _ => b • A := Matrix.kronecker_diagonal _ _ |>.trans <| by
    congr! 2
    ext
    simp [(Nat.cast_commute b _).eq]

