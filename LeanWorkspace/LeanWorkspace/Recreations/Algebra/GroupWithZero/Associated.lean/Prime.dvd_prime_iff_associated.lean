import Mathlib

variable {M : Type*}

theorem Prime.dvd_prime_iff_associated [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
    (pp : Prime p) (qp : Prime q) : p ∣ q ↔ Associated p q := pp.irreducible.dvd_irreducible_iff_associated qp.irreducible

