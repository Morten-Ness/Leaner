import Mathlib

variable {G H I : Type*}

variable [Monoid G] [Monoid H] [Monoid I]

theorem Submonoid.exists_eq_mgraph {G : Submonoid (H × I)} (hG₁ : Function.Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = f.mgraph := by
  simpa using MonoidHom.exists_mrange_eq_mgraph hG₁.surjective
    fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hG₁.injective h)

