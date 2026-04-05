import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_mulIndicator (s t : Set α) (f : α → M) :
    Set.mulIndicator s (Set.mulIndicator t f) = Set.mulIndicator (s ∩ t) f := funext fun x => by
    simp only [Set.mulIndicator]
    split_ifs <;> simp_all +contextual

