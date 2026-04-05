import Mathlib

open scoped Pointwise

variable {α β : Type*}

theorem smul_set_pi₀' {M ι : Type*} {α : ι → Type*} [GroupWithZero M] [∀ i, MulAction M (α i)]
    {c : M} {I : Set ι} (h : c ≠ 0 ∨ I = univ) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := h.elim (fun hc ↦ smul_set_pi_of_isUnit (.mk0 _ hc) I s) (fun hI ↦ hI ▸ smul_set_univ_pi ..)

