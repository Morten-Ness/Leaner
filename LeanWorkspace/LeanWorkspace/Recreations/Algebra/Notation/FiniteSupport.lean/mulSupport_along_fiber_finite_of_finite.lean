import Mathlib

variable {α β γ : Type*} [One γ]

theorem mulSupport_along_fiber_finite_of_finite (f : α × β → γ) (a : α) (h : HasFiniteMulSupport f) :
    HasFiniteMulSupport fun b ↦ f (a, b) := (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

