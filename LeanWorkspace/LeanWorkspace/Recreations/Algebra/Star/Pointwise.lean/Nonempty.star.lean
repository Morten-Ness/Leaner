import Mathlib

variable {α : Type*} {s t : Set α} {a : α}

theorem Nonempty.star [InvolutiveStar α] {s : Set α} (h : s.Nonempty) : s⋆.Nonempty := Set.nonempty_star.2 h

