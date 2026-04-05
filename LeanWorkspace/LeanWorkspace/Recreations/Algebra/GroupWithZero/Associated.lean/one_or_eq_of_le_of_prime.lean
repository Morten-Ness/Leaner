import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem one_or_eq_of_le_of_prime {p m : Associates M} (hp : Prime p) (hle : m ≤ p) :
    m = 1 ∨ m = p := by
  rcases Associates.mk_surjective p with ⟨p, Associated.rfl⟩
  rcases Associates.mk_surjective m with ⟨m, Associated.rfl⟩
  simpa [Associates.mk_eq_mk_iff_associated, Associated.comm]
    using (Associates.prime_mk.1 hp).irreducible.dvd_iff.mp (Associates.mk_le_mk_iff_dvd.1 hle)

