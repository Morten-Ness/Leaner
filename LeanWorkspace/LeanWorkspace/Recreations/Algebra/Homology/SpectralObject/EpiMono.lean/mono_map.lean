import Mathlib

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

theorem mono_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : ℤ)
    (hα₁ : α.app 1 = 𝟙 _ := by cat_disch) (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hα₃ : α.app 3 = 𝟙 _ := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Mono (X.map f₁ f₂ f₃ f₁' f₂ f₃ α n₀ n₁ n₂ hn₁ hn₂) := by
  have := X.map_ιE  _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [opcyclesMap_id, comp_id] at this
  exact mono_of_mono_fac this

