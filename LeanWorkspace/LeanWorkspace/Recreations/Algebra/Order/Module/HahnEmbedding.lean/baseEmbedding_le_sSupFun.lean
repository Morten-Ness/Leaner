import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

theorem baseEmbedding_le_sSupFun {c : Set (HahnEmbedding.Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : seed.baseEmbedding ≤ HahnEmbedding.Partial.sSupFun hc := by
  obtain ⟨f, hf⟩ := hnonempty
  exact le_trans f.prop.baseEmbedding_le (HahnEmbedding.Partial.le_sSupFun hc hf)

