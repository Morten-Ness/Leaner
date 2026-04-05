import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_compl_mul_self (s : Set α) (f : α → M) :
    mulIndicator sᶜ f * mulIndicator s f = f := funext <| Set.mulIndicator_compl_mul_self_apply s f

