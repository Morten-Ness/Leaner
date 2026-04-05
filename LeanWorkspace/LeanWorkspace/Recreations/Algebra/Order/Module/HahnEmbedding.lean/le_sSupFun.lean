import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem le_sSupFun {c : Set (HahnEmbedding.Partial seed)} (hc : DirectedOn (· ≤ ·) c)
    {f : HahnEmbedding.Partial seed} (hf : f ∈ c) :
    f.val ≤ HahnEmbedding.Partial.sSupFun hc := LinearPMap.le_sSup _ <| (Set.mem_image _ _ _).mpr ⟨f, hf, rfl⟩

