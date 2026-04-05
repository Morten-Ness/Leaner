import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {K : Type*} [Field K] [CharZero K] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
  [Module K M] [LieModule K L M]
  [IsTriangularizable K H M] [FiniteDimensional K M]

theorem LieAlgebra.isNilpotent_ad_of_mem_rootSpace
    [IsTriangularizable K H L] [FiniteDimensional K L]
    {x : L} {χ : H → K} (hχ : χ ≠ 0) (hx : x ∈ rootSpace H χ) :
    _root_.IsNilpotent (ad K L x) := isNilpotent_toEnd_of_mem_rootSpace (M := L) H hχ hx

