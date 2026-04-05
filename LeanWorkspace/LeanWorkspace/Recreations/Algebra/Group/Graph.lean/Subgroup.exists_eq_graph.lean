import Mathlib

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem Subgroup.exists_eq_graph {G : Subgroup (H × I)} (hG₁ : Function.Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = f.graph := by
  simpa [SetLike.ext_iff] using Submonoid.exists_eq_mgraph hG₁

