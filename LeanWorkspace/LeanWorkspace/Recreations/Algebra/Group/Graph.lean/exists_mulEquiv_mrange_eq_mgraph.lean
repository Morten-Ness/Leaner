import Mathlib

variable {G H I : Type*}

variable [Monoid G] [Monoid H] [Monoid I]

theorem exists_mulEquiv_mrange_eq_mgraph {f : G →* H × I} (hf₁ : Function.Surjective (Prod.fst ∘ f))
    (hf₂ : Function.Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃* I, mrange f = e.toMonoidHom.mgraph := by
  obtain ⟨e₁, he₁⟩ := MonoidHom.exists_mrange_eq_mgraph f hf₁ fun _ _ ↦ (hf _ _).1
  obtain ⟨e₂, he₂⟩ := MonoidHom.exists_mrange_eq_mgraph (MulEquiv.prodComm.toMonoidHom.comp f) (by simpa) <|
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [SetLike.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff_eq_swap])
  exact ⟨
  { toFun := e₁
    map_mul' := e₁.map_mul'
    invFun := e₂
    left_inv := fun h ↦ by rw [← he₁₂]
    right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

