import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem eq_zero_of_apply_eq_zero_of_mem_corootSpace
    (x : H) (α : H → K) (hαx : α x = 0) (hx : x ∈ corootSpace α) :
    x = 0 := by
  rcases eq_or_ne α 0 with rfl | hα; · simpa using hx
  replace hx : x ∈ ⨅ β : Weight K H L, β.ker := by
    refine (Submodule.mem_iInf _).mpr fun β ↦ ?_
    obtain ⟨a, b, hb, hab⟩ :=
      exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα β.genWeightSpace_ne_bot
    simpa [hαx, hb.ne'] using hab _ hx
  simpa using hx

