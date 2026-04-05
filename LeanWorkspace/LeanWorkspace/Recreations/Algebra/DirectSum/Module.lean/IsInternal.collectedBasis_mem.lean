import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem IsInternal.collectedBasis_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Module.Basis (α i) R (A i)) (a : Σ i, α i) : h.collectedBasis v a ∈ A a.1 := by simp

