import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem baseEmbedding_le_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : seed.baseEmbedding ≤ f.extendFun hx := by
  rw [HahnEmbedding.Partial.extendFun]
  exact le_trans f.prop.baseEmbedding_le <| LinearPMap.left_le_sup _ _ _

