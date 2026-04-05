import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

theorem eval_zero [IsOrderedAddMonoid R] [Archimedean R] : f.eval 0 = 0 := by
  unfold HahnEmbedding.Partial.eval
  convert toLex_zero
  ext c
  rw [HahnEmbedding.Partial.evalCoeff_eq f (y := 0) (by simp)]
  simp

