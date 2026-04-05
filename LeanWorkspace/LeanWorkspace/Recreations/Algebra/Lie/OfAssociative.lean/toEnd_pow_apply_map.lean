import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
  (f : M →ₗ⁅R,L⁆ M₂) (k : ℕ) (x : L)

theorem toEnd_pow_apply_map (m : M) :
    (toEnd R L M₂ x ^ k) (f m) = f ((toEnd R L M x ^ k) m) := LinearMap.congr_fun (LieModule.toEnd_pow_comp_lieHom f k x) m

