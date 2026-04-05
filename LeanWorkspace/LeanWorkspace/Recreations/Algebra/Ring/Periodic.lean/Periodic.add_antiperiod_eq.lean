import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.add_antiperiod_eq [AddMonoid α] [Neg β] (h1 : Function.Periodic f c₁)
    (h2 : Function.Antiperiodic f c₂) : f (c₁ + c₂) = -f 0 := (h1.add_antiperiod h2).eq

