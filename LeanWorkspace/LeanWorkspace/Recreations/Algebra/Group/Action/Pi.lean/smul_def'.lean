import Mathlib

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

theorem smul_def' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : s • x = fun i ↦ s i • x i := rfl

