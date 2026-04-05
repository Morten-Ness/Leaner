import Mathlib

section

variable {M : Type*}

variable [Monoid M] {p q a b : M}

theorem Irreducible.eq_one_or_eq_one [Subsingleton Mˣ] (hab : Irreducible (a * b)) :
    a = 1 ∨ b = 1 := by simpa using hab.isUnit_or_isUnit rfl

end

section

variable {M : Type*}

variable [Monoid M] {p q a b : M}

theorem Irreducible.ne_one (hp : Irreducible p) : p ≠ 1 := by rintro rfl; exact not_irreducible_one hp

end

section

variable {M : Type*}

variable [Monoid M] {p q a b : M}

theorem irreducible_or_factor (hp : ¬IsUnit p) :
    Irreducible p ∨ ∃ a b, ¬IsUnit a ∧ ¬IsUnit b ∧ p = a * b := by
  simpa [irreducible_iff, hp, and_rotate] using em (∀ a b, p = a * b → IsUnit a ∨ IsUnit b)

end
