import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem nonempty_star [InvolutiveStar α] {s : Set α} : s⋆.Nonempty ↔ s.Nonempty := star_involutive.surjective.nonempty_preimage

