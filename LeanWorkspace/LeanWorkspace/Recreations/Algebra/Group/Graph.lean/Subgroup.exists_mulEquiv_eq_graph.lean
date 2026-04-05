import Mathlib

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem Subgroup.exists_mulEquiv_eq_graph {G : Subgroup (H × I)}
    (hG₁ : Function.Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Function.Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using Submonoid.exists_mulEquiv_eq_mgraph hG₁ hG₂

