import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

theorem prod_snd_fst : Pi.prod (Prod.snd : α × β → β) (Prod.fst : α × β → α) = .swap := rfl

