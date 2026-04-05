import Mathlib

variable {ι : Type*} {M N : Type*} {α : ι → Type*}

variable [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σ i, α i)

theorem smul_mk : a • Sigma.mk i b = ⟨i, a • b⟩ := rfl

