import Mathlib

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

theorem smul_apply' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : (s • x) i = s i • x i := rfl

