import Mathlib

variable {α : Type u} {β : Type v} {γ : Type w}

variable [Mul α] [Mul β] [Mul γ]

theorem _root_.MulEquiv.withOneCongr_symm (e : α ≃* β) :
    e.withOneCongr.symm = e.symm.withOneCongr := rfl

