import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_congr (h : EqOn f g s) : Set.mulIndicator s f = Set.mulIndicator s g := funext fun x => by
    simp only [Set.mulIndicator]
    split_ifs with h_1
    · exact h h_1
    rfl

