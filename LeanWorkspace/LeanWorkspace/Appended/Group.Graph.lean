import Mathlib

section

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem Subgroup.exists_eq_graph {G : Subgroup (H × I)} (hG₁ : Function.Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = f.graph := by
  simpa [SetLike.ext_iff] using Submonoid.exists_eq_mgraph hG₁

end

section

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem Subgroup.exists_mulEquiv_eq_graph {G : Subgroup (H × I)}
    (hG₁ : Function.Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Function.Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using Submonoid.exists_mulEquiv_eq_mgraph hG₁ hG₂

end

section

variable {G H I : Type*}

variable [Monoid G] [Monoid H] [Monoid I]

theorem Submonoid.exists_eq_mgraph {G : Submonoid (H × I)} (hG₁ : Function.Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →* I, G = f.mgraph := by
  simpa using MonoidHom.exists_mrange_eq_mgraph hG₁.surjective
    fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hG₁.injective h)

end

section

variable {G H I : Type*}

variable [Monoid G] [Monoid H] [Monoid I]

theorem Submonoid.exists_mulEquiv_eq_mgraph {G : Submonoid (H × I)}
    (hG₁ : Function.Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Function.Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃* I, G = e.toMonoidHom.mgraph := by
  simpa using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hG₁.surjective hG₂.surjective
    fun _ _ ↦ hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

end

section

variable {G H I : Type*}

variable [Monoid G] [Monoid H] [Monoid I]

theorem exists_mrange_eq_mgraph {f : G →* H × I} (hf₁ : Function.Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →* I, mrange f = f'.mgraph := by
  obtain ⟨f', hf'⟩ := exists_range_eq_graphOn_univ hf₁ hf
  simp only [Set.ext_iff, Set.mem_range, mem_graphOn, mem_univ, true_and, Prod.forall] at hf'
  use
  { toFun := f'
    map_one' := (hf' _ _).1 ⟨1, map_one _⟩
    map_mul' := by
      simp_rw [hf₁.forall]
      rintro g₁ g₂
      exact (hf' _ _).1 ⟨g₁ * g₂, by simp [Prod.ext_iff, (hf' (f _).1 _).1 ⟨_, rfl⟩]⟩ }
  simpa [SetLike.ext_iff] using hf'

end

section

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

end

section

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem exists_mulEquiv_range_eq_graph {f : G →* H × I} (hf₁ : Function.Surjective (Prod.fst ∘ f))
    (hf₂ : Function.Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃* I, Set.range f = e.toMonoidHom.graph := by
  simpa [SetLike.ext_iff] using MonoidHom.exists_mulEquiv_mrange_eq_mgraph hf₁ hf₂ hf

end

section

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

theorem exists_range_eq_graph {f : G →* H × I} (hf₁ : Function.Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →* I, Set.range f = f'.graph := by
  simpa [SetLike.ext_iff] using MonoidHom.exists_mrange_eq_mgraph hf₁ hf

end
