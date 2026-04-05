import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem IsInternal.collectedBasis_repr_of_mem_ne (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Module.Basis (α i) R (A i)) {x : M} {i j : ι} (hij : i ≠ j) {a : α j} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨j, a⟩ = 0 := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem_ne hij hx]

