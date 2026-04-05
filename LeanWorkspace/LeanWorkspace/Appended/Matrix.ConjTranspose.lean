import Mathlib

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_injective [InvolutiveStar α] :
    Function.Injective (Matrix.conjTranspose : Matrix m n α → Matrix n m α) := (map_injective star_injective).comp transpose_injective

end
