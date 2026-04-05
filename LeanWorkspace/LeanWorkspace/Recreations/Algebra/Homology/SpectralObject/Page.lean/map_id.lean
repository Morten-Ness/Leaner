import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  {i'' j'' k'' l'' : ι} (f₁'' : i'' ⟶ j'') (f₂'' : j'' ⟶ k'') (f₃'' : k'' ⟶ l'')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (β : mk₃ f₁' f₂' f₃' ⟶ mk₃ f₁'' f₂'' f₃'')
  (γ : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁'' f₂'' f₃'')
  (n₀ n₁ n₂ : ℤ)

theorem map_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  dsimp only [CategoryTheory.Abelian.SpectralObject.map]
  simp [CategoryTheory.Abelian.SpectralObject.shortComplexMap_id, ShortComplex.homologyMap_id]
  rfl

