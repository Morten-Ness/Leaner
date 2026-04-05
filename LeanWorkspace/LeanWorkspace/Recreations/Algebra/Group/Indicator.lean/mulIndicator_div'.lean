import Mathlib

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem mulIndicator_div' (s : Set α) (f g : α → G) :
    mulIndicator s (f / g) = mulIndicator s f / mulIndicator s g := Set.mulIndicator_div s f g

