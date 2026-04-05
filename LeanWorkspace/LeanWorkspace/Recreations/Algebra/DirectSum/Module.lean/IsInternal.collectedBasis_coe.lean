import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

set_option backward.isDefEq.respectTransparency false in
theorem IsInternal.collectedBasis_coe (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Module.Basis (α i) R (A i)) : ⇑(h.collectedBasis v) = fun a : Σ i, α i ↦ ↑(v a.1 a.2) := by
  simp [DirectSum.IsInternal.collectedBasis, DirectSum.coeLinearMap, DFinsupp.mapRange.linearEquiv,
    DirectSum.toModule, DFinsupp.lsum]

