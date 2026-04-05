import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable [DecompositionMonoid α]

theorem IsRelPrime.mul_left (H1 : IsRelPrime x z) (H2 : IsRelPrime y z) : IsRelPrime (x * y) z := fun _ h hz ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
    exact (H1 ha <| (Units.dvd_mul_right a b).trans hz).mul (H2 hb <| (Units.dvd_mul_left b a).trans hz)

