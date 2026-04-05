import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Function.Surjective f) :
    map f ⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆ := by
  suffices ⁅map f I₁, map f I₂⁆ ≤ map f ⁅I₁, I₂⁆ by exact le_antisymm (LieIdeal.map_bracket_le f) this
  rw [← LieSubmodule.toSubmodule_le_toSubmodule, coe_map_of_surjective h,
    LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LinearMap.map_span]
  apply Submodule.span_mono
  rintro x ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩, rfl⟩
  obtain ⟨y₁, rfl⟩ := mem_map_of_surjective h h₁
  obtain ⟨y₂, rfl⟩ := mem_map_of_surjective h h₂
  exact ⟨⁅(y₁ : L), (y₂ : L)⁆, ⟨y₁, y₂, rfl⟩, by apply f.map_lie⟩

