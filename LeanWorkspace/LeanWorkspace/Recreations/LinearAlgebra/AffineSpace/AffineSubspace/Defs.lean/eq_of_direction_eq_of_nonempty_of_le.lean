import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : AffineSubspace k P}
    (hd : s₁.direction = s₂.direction) (hn : (s₁ : Set P).Nonempty) (hle : s₁ ≤ s₂) : s₁ = s₂ := let ⟨p, hp⟩ := hn
  AffineSubspace.ext_of_direction_eq hd ⟨p, hp, hle hp⟩

