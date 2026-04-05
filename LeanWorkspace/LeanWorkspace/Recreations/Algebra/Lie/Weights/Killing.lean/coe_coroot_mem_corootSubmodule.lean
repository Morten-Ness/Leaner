import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

omit [CharZero K] in
theorem coe_coroot_mem_corootSubmodule (α : Weight K H L) :
    (LieAlgebra.IsKilling.coroot α : L) ∈ corootSubmodule α := (LieSubmodule.mem_map _).mpr
    ⟨⟨LieAlgebra.IsKilling.coroot α, (LieAlgebra.IsKilling.coroot α).property⟩, coroot_mem_corootSpace α, rfl⟩

