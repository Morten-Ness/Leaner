import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem eq_coroot_of_mem_corootSpace_of_two (α : Weight K H L) {x : H}
    (h_mem : x ∈ corootSpace α) (h_two : α x = 2) :
    x = LieAlgebra.IsKilling.coroot α := by
  by_cases h₀ : α.IsZero; · simp [h₀.eq] at h_two
  replace h_mem : x ∈ K ∙ LieAlgebra.IsKilling.coroot α := by rwa [← LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton]
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp h_mem
  suffices t = 1 by simp [this]
  simpa [LieAlgebra.IsKilling.root_apply_coroot h₀] using h_two

