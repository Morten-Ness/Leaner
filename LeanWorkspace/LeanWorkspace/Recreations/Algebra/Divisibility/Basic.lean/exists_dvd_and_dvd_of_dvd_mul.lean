import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem exists_dvd_and_dvd_of_dvd_mul [DecompositionMonoid α] {b c a : α} (H : a ∣ b * c) :
    ∃ a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂ := DecompositionMonoid.primal a H

