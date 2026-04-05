import Mathlib

open scoped Pointwise

variable {α β : Type*}

theorem smul_set_pi₀ {M ι : Type*} {α : ι → Type*} [GroupWithZero M] [∀ i, MulAction M (α i)]
    {c : M} (hc : c ≠ 0) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := smul_set_pi_of_isUnit (.mk0 _ hc) I s

