import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem irreducible_iff_prime_iff :
    (∀ a : M, Irreducible a ↔ Prime a) ↔ ∀ a : Associates M, Irreducible a ↔ Prime a := by
  simp_rw [Associates.forall_associated, Associates.irreducible_mk, Associates.prime_mk]

