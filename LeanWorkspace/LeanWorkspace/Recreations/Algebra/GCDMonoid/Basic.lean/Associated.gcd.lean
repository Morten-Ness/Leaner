import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem Associated.gcd [GCDMonoid α]
    {a₁ a₂ b₁ b₂ : α} (ha : Associated a₁ a₂) (hb : Associated b₁ b₂) :
    Associated (gcd a₁ b₁) (gcd a₂ b₂) := associated_of_dvd_dvd (gcd_dvd_gcd ha.dvd hb.dvd) (gcd_dvd_gcd ha.dvd' hb.dvd')

