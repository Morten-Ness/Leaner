import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_submatrix [Star α] (A : Matrix m n α) (r : l → m)
    (c : o → n) : (A.submatrix r c)ᴴ = Aᴴ.submatrix c r := ext fun _ _ => rfl

