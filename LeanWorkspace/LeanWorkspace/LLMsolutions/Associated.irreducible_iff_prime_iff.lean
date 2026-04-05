FAIL
import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem irreducible_iff_prime_iff :
    (∀ a : M, Irreducible a ↔ Prime a) ↔ ∀ a : Associates M, Irreducible a ↔ Prime a := by
  constructor
  · intro h a
    constructor
    · intro ha
      rcases Quotient.exists_rep a with ⟨b, rfl⟩
      exact (associates_irreducible_iff_prime (a := b)).2 ((h b).1 ha)
    · intro ha
      rcases Quotient.exists_rep a with ⟨b, rfl⟩
      exact (h b).2 ((associates_irreducible_iff_prime (a := b)).1 ha)
  · intro h a
    constructor
    · intro ha
      exact (associates_irreducible_iff_prime (a := a)).1 ((h (Associates.mk a)).1 <| associates_irreducible_iff_prime (a := a).2 ha)
    · intro ha
      exact (associates_irreducible_iff_prime (a := a)).2 ((h (Associates.mk a)).2 <| associates_irreducible_iff_prime (a := a).1 ha)
