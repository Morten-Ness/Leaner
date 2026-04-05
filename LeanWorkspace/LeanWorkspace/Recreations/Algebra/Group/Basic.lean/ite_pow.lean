import Mathlib

variable {α β G M : Type*}

variable [Pow α β]

theorem ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) :
    (if p then a else b) ^ c = if p then a ^ c else b ^ c := dite_pow _ _ _ _

