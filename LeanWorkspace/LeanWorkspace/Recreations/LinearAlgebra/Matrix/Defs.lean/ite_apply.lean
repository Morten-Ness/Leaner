import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem ite_apply (P : Prop) [Decidable P]
    (A : Matrix m n α) (B : Matrix m n α) (i : m) (j : n) :
    (if P then A else B) i j = if P then A i j else B i j := Matrix.dite_apply _ _ _ _ _

