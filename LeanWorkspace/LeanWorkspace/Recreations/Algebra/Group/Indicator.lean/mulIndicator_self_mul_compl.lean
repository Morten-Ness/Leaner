import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_self_mul_compl (s : Set α) (f : α → M) :
    mulIndicator s f * mulIndicator sᶜ f = f := funext <| Set.mulIndicator_self_mul_compl_apply s f

