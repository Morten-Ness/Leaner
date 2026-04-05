import Mathlib

variable {F α β γ : Type*}

variable [VSub α β] {s t : Set β}

theorem Finite.vsub (hs : s.Finite) (ht : t.Finite) : Set.Finite (s -ᵥ t) := hs.image2 _ ht

