import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem lie_mem_genWeightSpace_of_mem_genWeightSpace {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ genWeightSpace M χ₂) :
    ⁅x, m⁆ ∈ genWeightSpace M (χ₁ + χ₂) := by
  rw [genWeightSpace, LieSubmodule.mem_iInf]
  intro y
  replace hx : x ∈ genWeightSpaceOf L (χ₁ y) y := by
    rw [rootSpace, genWeightSpace, LieSubmodule.mem_iInf] at hx; exact hx y
  replace hm : m ∈ genWeightSpaceOf M (χ₂ y) y := by
    rw [genWeightSpace, LieSubmodule.mem_iInf] at hm; exact hm y
  exact lie_mem_maxGenEigenspace_toEnd hx hm

