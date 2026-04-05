import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_involutive [InvolutiveStar α] :
    (Matrix.conjTranspose : Matrix n n α → Matrix n n α).Involutive := Matrix.conjTranspose_conjTranspose

