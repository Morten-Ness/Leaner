import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_pow_left_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : ℕ} : gcd (a ^ k) b ∣ gcd a b ^ k := calc
    gcd (a ^ k) b ∣ gcd b (a ^ k) := (gcd_comm' _ _).dvd
    _ ∣ gcd b a ^ k := gcd_pow_right_dvd_pow_gcd
    _ ∣ gcd a b ^ k := pow_dvd_pow_of_dvd (gcd_comm' _ _).dvd _

