import Mathlib

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem exists_mulEquiv_range_eq_graph {f : G →* H × I} (hf₁ : Function.Surjective (Prod.fst ∘ f))
    (hf₂ : Function.Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃* I, Set.range f = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hf₁ hf₂ hf

