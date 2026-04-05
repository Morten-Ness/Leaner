import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

theorem prod_fst_snd : Pi.prod (Prod.fst : α × β → α) (Prod.snd : α × β → β) = id := rfl

