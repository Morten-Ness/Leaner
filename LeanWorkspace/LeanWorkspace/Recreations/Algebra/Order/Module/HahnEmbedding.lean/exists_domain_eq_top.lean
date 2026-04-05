import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem exists_domain_eq_top [IsOrderedAddMonoid R] [Archimedean R] :
    ∃ f : HahnEmbedding.Partial seed, f.val.domain = ⊤ := by
  obtain ⟨f, hf⟩ := HahnEmbedding.Partial.exists_isMax seed
  refine ⟨f, Submodule.eq_top_iff'.mpr ?_⟩
  rw [isMax_iff_forall_not_lt] at hf
  contrapose! hf with hx
  obtain ⟨x, hx⟩ := hx
  exact ⟨f.extend hx, HahnEmbedding.Partial.lt_extend f hx⟩

