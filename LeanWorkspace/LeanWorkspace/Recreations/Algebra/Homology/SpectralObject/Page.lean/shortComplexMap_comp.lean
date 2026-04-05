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

theorem shortComplexMap_comp (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) n₀ n₁ n₂ hn₁ hn₂  =
    X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      X.shortComplexMap f₁' f₂' f₃' f₁'' f₂'' f₃'' β n₀ n₁ n₂ hn₁ hn₂ := by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

