import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem Finite.star [InvolutiveStar α] {s : Set α} (hs : s.Finite) : s⋆.Finite := hs.preimage star_injective.injOn

