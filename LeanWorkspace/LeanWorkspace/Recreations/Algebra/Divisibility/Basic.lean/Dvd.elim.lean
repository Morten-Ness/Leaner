import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P := Exists.elim H₁ H₂

attribute [local simp] mul_assoc mul_comm mul_left_comm

