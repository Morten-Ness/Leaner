import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅I₁, I₂⁆ ≤ ⁅map f I₁, map f I₂⁆ := by
  rw [map_le_iff_le_comap, LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  intro x hx
  obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx
  rw [← hx]
  let fy₁ : ↥(map f I₁) := ⟨f y₁, mem_map hy₁⟩
  let fy₂ : ↥(map f I₂) := ⟨f y₂, mem_map hy₂⟩
  change _ ∈ comap f ⁅map f I₁, map f I₂⁆
  simp only [mem_comap, LieHom.map_lie]
  exact LieSubmodule.lie_coe_mem_lie fy₁ fy₂

