import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem dite_apply (P : Prop) [Decidable P]
    (A : P → Matrix m n α) (B : ¬P → Matrix m n α) (i : m) (j : n) :
    dite P A B i j = dite P (A · i j) (B · i j) := by
  rw [dite_apply, dite_apply]

