import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem of_nsmul {n : ℕ} : a ≡ b [PMOD n • p] → a ≡ b [PMOD p] := fun ⟨k, l, h⟩ =>
  ⟨k * n, l * n, by simpa [mul_nsmul']⟩

