import Mathlib

variable {m n α β : Type*}

theorem intrinsicStar_def [Star α] (x : WithConv (Matrix m n α)) :
    star x = toConv (x.ofConv.map star) := rfl

attribute [local simp] intrinsicStar_def

