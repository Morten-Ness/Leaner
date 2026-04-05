import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div (a b : G) : |a / b|ₘ ≤ |a|ₘ * |b|ₘ := by
  rw [div_eq_mul_inv, ← mabs_inv b]
  exact mabs_mul_le a _

