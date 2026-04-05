import Mathlib

variable {m n α β : Type*}

theorem convOne_def [One α] : (1 : WithConv (Matrix m n α)) = toConv (of 1) := rfl

attribute [local simp] convOne_def

