import Mathlib

variable {α β G M : Type*}

variable [Pow α β]

theorem pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) :
    a ^ (if p then b else c) = if p then a ^ b else a ^ c := pow_dite _ _ _ _

