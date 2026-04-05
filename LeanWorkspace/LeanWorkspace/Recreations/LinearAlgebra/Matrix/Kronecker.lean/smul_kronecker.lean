import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem smul_kronecker [Mul α] [SMul R α] [IsScalarTower R α α] (r : R)
    (A : Matrix l m α) (B : Matrix n p α) : (r • A) ⊗ₖ B = r • A ⊗ₖ B := Matrix.kroneckerMap_smul_left _ _ (fun _ _ => smul_mul_assoc _ _ _) _ _

