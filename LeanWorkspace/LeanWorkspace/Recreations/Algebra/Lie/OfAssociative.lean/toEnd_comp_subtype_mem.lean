import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable {N : LieSubmodule R L M} {x : L}

theorem toEnd_comp_subtype_mem (m : M) (hm : m ∈ (N : Submodule R M)) :
    (toEnd R L M x).comp (N : Submodule R M).subtype ⟨m, hm⟩ ∈ (N : Submodule R M) := by
  simpa using N.lie_mem hm

