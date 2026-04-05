import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_antiperiod_eq [AddGroup α] [InvolutiveNeg β] (h1 : Function.Periodic f c₁)
    (h2 : Function.Antiperiodic f c₂) : f (c₁ - c₂) = -f 0 := (h1.sub_antiperiod h2).eq

