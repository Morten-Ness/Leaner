import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem star_apply [Star α] (M : Matrix n n α) (i j) : (star M) i j = star (M j i) := rfl

