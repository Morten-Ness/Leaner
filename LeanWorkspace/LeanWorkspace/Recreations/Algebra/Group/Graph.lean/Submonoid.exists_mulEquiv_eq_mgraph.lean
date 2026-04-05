import Mathlib

variable {G H I : Type*}

variable [Monoid G] [Monoid H] [Monoid I]

theorem Submonoid.exists_mulEquiv_eq_mgraph {G : Submonoid (H × I)}
    (hG₁ : Function.Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Function.Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = e.toMonoidHom.mgraph := by
  simpa using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hG₁.surjective hG₂.surjective
    fun _ _ ↦ hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

