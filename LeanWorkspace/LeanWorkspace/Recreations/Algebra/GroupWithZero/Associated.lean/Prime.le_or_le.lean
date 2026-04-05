import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem Prime.le_or_le {p : Associates M} (hp : Prime p) {a b : Associates M} (h : p ≤ a * b) :
    p ≤ a ∨ p ≤ b := hp.2.2 a b h

