import Mathlib

variable {M : Type*}

theorem trans [Monoid M] : ∀ {x y z : M}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
  | x, _, _, ⟨u, Associated.rfl⟩, ⟨v, Associated.rfl⟩ => ⟨u * v, by rw [Units.val_mul, mul_assoc]⟩
