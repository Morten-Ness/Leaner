import Mathlib

variable {M : Type*}

theorem Prime.associated_of_dvd [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M}
    (p_prime : Prime p) (q_prime : Prime q) (dvd : p ∣ q) : Associated p q := p_prime.irreducible.associated_of_dvd q_prime.irreducible dvd

