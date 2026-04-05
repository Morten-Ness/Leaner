import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

theorem _root_.LieHom.range_eq_ker_iff (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) :
    i.range = p.ker ↔ Exact i p := ⟨fun h x ↦ by simp [← LieHom.coe_range, h], fun h ↦ (p.ker.toLieSubalgebra.ext i.range h).symm⟩

