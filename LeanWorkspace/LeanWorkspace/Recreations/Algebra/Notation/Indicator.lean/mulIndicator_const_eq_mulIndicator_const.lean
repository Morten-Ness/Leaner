import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_const_eq_mulIndicator_const {t : Set β} {b : β} {c : M} (h : a ∈ s ↔ b ∈ t) :
    s.mulIndicator (fun _ ↦ c) a = t.mulIndicator (fun _ ↦ c) b := Set.mulIndicator_eq_mulIndicator h rfl

