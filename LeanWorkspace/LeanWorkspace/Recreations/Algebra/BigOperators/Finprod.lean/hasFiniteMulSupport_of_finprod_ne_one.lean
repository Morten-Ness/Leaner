import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem hasFiniteMulSupport_of_finprod_ne_one {f : α → M} (h : ∏ᶠ i, f i ≠ 1) :
    HasFiniteMulSupport f := not_infinite.mp <| (finprod_of_infinite_mulSupport ·).mt h

