import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable [LieAlgebra R L]

variable (K : LieSubalgebra R L)

theorem exists_lieIdeal_coe_eq_iff :
    (∃ I : LieIdeal R L, ↑I = K) ↔ ∀ x y : L, y ∈ K → ⁅x, y⁆ ∈ K := by
  simp only [← toSubmodule_inj, LieIdeal.toLieSubalgebra_toSubmodule,
    Submodule.exists_lieSubmodule_coe_eq_iff L, mem_toSubmodule]

