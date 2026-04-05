import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem coe_smul_finset (a : α) (s : Finset β) : ↑(a • s) = a • (↑s : Set β) := coe_image

