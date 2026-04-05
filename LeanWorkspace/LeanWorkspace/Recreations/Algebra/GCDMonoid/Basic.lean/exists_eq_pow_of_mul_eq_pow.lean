import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem exists_eq_pow_of_mul_eq_pow [GCDMonoid α] [Subsingleton αˣ]
    {a b c : α} (hab : IsUnit (gcd a b)) {k : ℕ} (h : a * b = c ^ k) : ∃ d : α, a = d ^ k := let ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hab h
  ⟨d, (associated_iff_eq.mp hd).symm⟩

