import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty := hs.image _

