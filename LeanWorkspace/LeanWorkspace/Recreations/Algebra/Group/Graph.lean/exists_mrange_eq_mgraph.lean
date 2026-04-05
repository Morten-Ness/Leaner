import Mathlib

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

