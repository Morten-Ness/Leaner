import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) :
    (-A) i j = -(A i j) := rfl

set_option backward.isDefEq.respectTransparency false in

