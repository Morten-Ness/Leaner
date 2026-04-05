import Mathlib

variable {G H M N α : Type*}

theorem smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUnit m) (a : α) : hm.unit • a = m • a := rfl

