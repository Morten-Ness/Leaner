import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_sub (a b : G) : a ≡ b [PMOD b - a] := ⟨1, 0, by simp [one_nsmul]⟩

