import Mathlib

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem mulIndicator_inv (s : Set α) (f : α → G) :
    (mulIndicator s fun a => (f a)⁻¹) = fun a => (mulIndicator s f a)⁻¹ := Set.mulIndicator_inv' s f

