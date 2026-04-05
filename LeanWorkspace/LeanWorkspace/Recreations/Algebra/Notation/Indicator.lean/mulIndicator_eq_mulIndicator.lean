import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_eq_mulIndicator {t : Set β} {g : β → M} {b : β}
    (h1 : a ∈ s ↔ b ∈ t) (h2 : f a = g b) :
    s.mulIndicator f a = t.mulIndicator g b := by
  by_cases a ∈ s <;> simp_all

