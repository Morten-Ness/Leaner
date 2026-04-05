import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem mk_le_mk_smul (a : M) (k : K) : ArchimedeanClass.mk a ≤ ArchimedeanClass.mk (k • a) := by
  obtain rfl | h := eq_or_ne k 0 <;> simp [*]

