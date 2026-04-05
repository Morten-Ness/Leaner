import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [GCDMonoid α] {m n a b c : α}

variable {p : α} (hp : Prime p)

theorem not_dvd_lcm (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ lcm a b := Prime.dvd_lcm hp.not.mpr <| not_or.mpr ⟨ha, hb⟩

