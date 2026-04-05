import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem isPrimal : IsPrimal p := fun _a _b dvd ↦ (Prime.dvd_or_dvd hp dvd).elim
  (fun h ↦ ⟨p, 1, h, one_dvd _, (mul_one p).symm⟩) fun h ↦ ⟨1, p, one_dvd _, h, (one_mul p).symm⟩

