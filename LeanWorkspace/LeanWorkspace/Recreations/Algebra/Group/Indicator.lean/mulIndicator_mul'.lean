import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_mul' (s : Set α) (f g : α → M) :
    mulIndicator s (f * g) = mulIndicator s f * mulIndicator s g := Set.mulIndicator_mul s f g

