import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem biUnion_smul_finset (s : Finset α) (t : Finset β) : s.biUnion (· • t) = s • t := biUnion_image_left

