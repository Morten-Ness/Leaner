import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem eq_symm_comp {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g := e.toEquiv.eq_symm_comp f g

