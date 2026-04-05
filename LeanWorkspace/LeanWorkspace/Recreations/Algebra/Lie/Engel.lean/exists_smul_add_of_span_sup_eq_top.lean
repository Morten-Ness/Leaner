import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {I : LieIdeal R L} {x : L} (hxI : R ∙ x ⊔ I = ⊤)

theorem exists_smul_add_of_span_sup_eq_top (y : L) : ∃ t : R, ∃ z ∈ I, y = t • x + z := by
  have hy : y ∈ (⊤ : Submodule R L) := Submodule.mem_top
  simp only [← hxI, Submodule.mem_sup, Submodule.mem_span_singleton] at hy
  obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy
  exact ⟨t, z, hz, rfl⟩

