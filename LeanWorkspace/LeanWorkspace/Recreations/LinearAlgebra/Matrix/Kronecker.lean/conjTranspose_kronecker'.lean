import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem conjTranspose_kronecker' [Mul R] [StarMul R] (x : Matrix l m R) (y : Matrix n p R) :
    (x ⊗ₖ y)ᴴ = (yᴴ ⊗ₖ xᴴ).submatrix Prod.swap Prod.swap := by
  ext; simp

