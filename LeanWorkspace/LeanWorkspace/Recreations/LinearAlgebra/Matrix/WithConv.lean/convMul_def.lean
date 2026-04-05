import Mathlib

variable {m n α β : Type*}

theorem convMul_def [Mul α] (x y : WithConv (Matrix m n α)) :
    x * y = toConv (x.ofConv ⊙ y.ofConv) := rfl

attribute [local simp] convMul_def

