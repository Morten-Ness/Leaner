import Mathlib

variable {G H M N α : Type*}

theorem smul_mk_apply {M α : Type*} [Monoid M] [SMul M α] (m n : M) (h₁) (h₂) (a : α) :
    (⟨m, n, h₁, h₂⟩ : Mˣ) • a = m • a := rfl

