import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem comap_bracket_le {J₁ J₂ : LieIdeal R L'} : ⁅comap f J₁, comap f J₂⁆ ≤ comap f ⁅J₁, J₂⁆ := by
  rw [← map_le_iff_le_comap]
  exact le_trans (LieIdeal.map_bracket_le f) (LieSubmodule.mono_lie LieSubmodule.map_comap_le LieSubmodule.map_comap_le)

