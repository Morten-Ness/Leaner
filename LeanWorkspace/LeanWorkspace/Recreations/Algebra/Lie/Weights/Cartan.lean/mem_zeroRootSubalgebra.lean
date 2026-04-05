import Mathlib

open scoped TensorProduct

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem mem_zeroRootSubalgebra (x : L) :
    x ∈ LieAlgebra.zeroRootSubalgebra R L H ↔ ∀ y : H, ∃ k : ℕ, (toEnd R H L y ^ k) x = 0 := by
  change x ∈ rootSpace H 0 ↔ _
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero]

