import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty := image_nonempty

