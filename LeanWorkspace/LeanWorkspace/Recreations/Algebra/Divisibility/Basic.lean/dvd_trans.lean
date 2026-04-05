import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem dvd_trans : a ∣ b → b ∣ c → a ∣ c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d * e, h₁ ▸ h₂.trans <| mul_assoc a d e⟩

alias Dvd.dvd.trans := dvd_trans

