import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

theorem exists_isMax [IsOrderedAddMonoid R] :
    ∃ f : HahnEmbedding.Partial seed, IsMax f := by
  apply zorn_le_nonempty
  intro c hc hnonempty
  exact ⟨HahnEmbedding.Partial.sSup hnonempty hc.directedOn, mem_upperBounds.mpr fun _ hf ↦ HahnEmbedding.Partial.le_sSupFun hc.directedOn hf⟩

