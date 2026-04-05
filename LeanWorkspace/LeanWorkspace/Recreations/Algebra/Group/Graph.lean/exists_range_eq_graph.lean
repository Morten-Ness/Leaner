import Mathlib

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem exists_range_eq_graph {f : G →* H × I} (hf₁ : Function.Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →* I, Set.range f = f'.graph := by
  simpa [SetLike.ext_iff] using MonoidHom.exists_mrange_eq_mgraph hf₁ hf

