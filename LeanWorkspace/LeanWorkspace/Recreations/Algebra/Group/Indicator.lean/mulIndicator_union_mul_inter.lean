import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_union_mul_inter (f : α → M) (s t : Set α) :
    mulIndicator (s ∪ t) f * mulIndicator (s ∩ t) f = mulIndicator s f * mulIndicator t f := funext <| Set.mulIndicator_union_mul_inter_apply f s t

