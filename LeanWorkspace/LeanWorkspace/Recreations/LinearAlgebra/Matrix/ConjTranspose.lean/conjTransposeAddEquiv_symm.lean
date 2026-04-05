import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTransposeAddEquiv_symm [AddMonoid α] [StarAddMonoid α] :
    (Matrix.conjTransposeAddEquiv m n α).symm = Matrix.conjTransposeAddEquiv n m α := rfl

