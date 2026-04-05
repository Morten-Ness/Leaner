import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem Associated.lcm [GCDMonoid α]
    {a₁ a₂ b₁ b₂ : α} (ha : Associated a₁ a₂) (hb : Associated b₁ b₂) :
    Associated (lcm a₁ b₁) (lcm a₂ b₂) := associated_of_dvd_dvd (lcm_dvd_lcm ha.dvd hb.dvd) (lcm_dvd_lcm ha.dvd' hb.dvd')

