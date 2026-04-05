import Mathlib

variable {M : Type*}

variable [Monoid M] {p q a b : M}

theorem irreducible_or_factor (hp : ¬IsUnit p) :
    Irreducible p ∨ ∃ a b, ¬IsUnit a ∧ ¬IsUnit b ∧ p = a * b := by
  simpa [irreducible_iff, hp, and_rotate] using em (∀ a b, p = a * b → IsUnit a ∨ IsUnit b)

