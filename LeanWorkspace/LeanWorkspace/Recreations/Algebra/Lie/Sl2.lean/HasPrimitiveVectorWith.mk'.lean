import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {h e f : L}

theorem HasPrimitiveVectorWith.mk' [IsAddTorsionFree M] (t : IsSl2Triple h e f) (m : M) (μ ρ : R)
    (hm : m ≠ 0) (hm' : ⁅h, m⁆ = μ • m) (he : ⁅e, m⁆ = ρ • m) :
    HasPrimitiveVectorWith t m μ where
  ne_zero := hm
  lie_h := hm'
  lie_e := by
    suffices 2 • ⁅e, m⁆ = 0 by simpa using this
    rw [← nsmul_lie, ← t.lie_h_e_nsmul, lie_lie, hm', lie_smul, he, lie_smul, hm',
      smul_smul, smul_smul, mul_comm ρ μ, sub_self]

