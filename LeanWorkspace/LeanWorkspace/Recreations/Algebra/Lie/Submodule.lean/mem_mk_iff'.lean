import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem mem_mk_iff' (p : Submodule R M) (h) {x : M} :
    x ∈ (⟨p, h⟩ : LieSubmodule R L M) ↔ x ∈ p := Iff.rfl

