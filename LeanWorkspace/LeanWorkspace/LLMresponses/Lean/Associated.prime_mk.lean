import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem prime_mk {p : M} : Prime (Associates.mk p) ↔ Prime p := by
  simpa using Associates.prime_mk_iff_prime p
