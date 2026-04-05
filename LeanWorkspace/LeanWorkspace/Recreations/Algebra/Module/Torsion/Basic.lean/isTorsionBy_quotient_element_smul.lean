import Mathlib

variable {R M : Type*}

variable (M) [CommRing R] [AddCommGroup M] [Module R M] (s : Set R) (r : R)

theorem isTorsionBy_quotient_element_smul :
    IsTorsionBy R (M ⧸ r • (⊤ : Submodule R M)) r := (Module.isTorsionBy_quotient_iff _ _).mpr (Submodule.smul_mem_pointwise_smul · r ⊤ ⟨⟩)

