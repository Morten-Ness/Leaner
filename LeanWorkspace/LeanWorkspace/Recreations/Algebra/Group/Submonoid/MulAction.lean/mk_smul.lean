import Mathlib

variable {M' : Type*} {α β : Type*}

variable [MulOneClass M']

variable [SMul M' α] {S : Submonoid M'}

theorem mk_smul (g : M') (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

