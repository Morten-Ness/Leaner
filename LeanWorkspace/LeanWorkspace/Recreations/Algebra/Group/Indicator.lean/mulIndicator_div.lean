import Mathlib

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem mulIndicator_div (s : Set α) (f g : α → G) :
    (mulIndicator s fun a => f a / g a) = fun a => mulIndicator s f a / mulIndicator s g a := (Set.mulIndicatorHom G s).map_div f g

