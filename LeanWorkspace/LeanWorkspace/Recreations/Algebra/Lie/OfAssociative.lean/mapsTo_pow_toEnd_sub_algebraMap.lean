import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable {N : LieSubmodule R L M} {x : L}

theorem mapsTo_pow_toEnd_sub_algebraMap {φ : R} {k : ℕ} {x : L} :
    MapsTo ((toEnd R L M x - algebraMap R (Module.End R M) φ) ^ k) N N := by
  rw [Module.End.coe_pow]
  exact MapsTo.iterate (fun m hm ↦ N.sub_mem (N.lie_mem hm) (N.smul_mem _ hm)) k

