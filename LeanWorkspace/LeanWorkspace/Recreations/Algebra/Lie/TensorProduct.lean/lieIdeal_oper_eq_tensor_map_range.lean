import Mathlib

open scoped TensorProduct

variable {R : Type u} [CommRing R]

variable {L : Type v} {M : Type w}

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (I : LieIdeal R L) (N : LieSubmodule R L M)

set_option backward.isDefEq.respectTransparency false in
theorem lieIdeal_oper_eq_tensor_map_range :
    ⁅I, N⁆ = ((LieModule.toModuleHom R L M).comp (TensorProduct.LieModule.mapIncl I N : I ⊗[R] N →ₗ⁅R,L⁆ L ⊗[R] M)).range := by
  rw [← toSubmodule_inj, lieIdeal_oper_eq_linear_span, LieModuleHom.toSubmodule_range,
    LieModuleHom.toLinearMap_comp, LinearMap.range_comp, TensorProduct.LieModule.mapIncl_def, TensorProduct.LieModule.toLinearMap_map,
    TensorProduct.range_map_eq_span_tmul, Submodule.map_span]
  congr; ext m; constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩; use x ⊗ₜ n; constructor
    · use ⟨x, hx⟩, ⟨n, hn⟩; rfl
    · simp
  · rintro ⟨t, ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, h⟩; rw [← h]; use ⟨x, hx⟩, ⟨n, hn⟩; rfl

