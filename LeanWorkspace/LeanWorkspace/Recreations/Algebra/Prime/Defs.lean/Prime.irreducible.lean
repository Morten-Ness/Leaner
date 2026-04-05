import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M] {p : M}

theorem Prime.irreducible (hp : Prime p) : Irreducible p := ⟨Prime.not_unit hp, fun a b ↦ by
    rintro rfl
    exact (Prime.dvd_or_dvd hp dvd_rfl).symm.imp
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_right <| right_ne_zero_of_mul Prime.ne_zero hp).mp <|
        dvd_mul_of_dvd_right · _)
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_left <| left_ne_zero_of_mul Prime.ne_zero hp).mp <|
        dvd_mul_of_dvd_left · _)⟩

