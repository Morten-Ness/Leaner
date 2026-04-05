import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ s) : l.prod ∈ s := list_prod_mem _root_ hl

