import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mem_mulSupport : x ∈ Function.mulSupport f ↔ f x ≠ 1 := .rfl

