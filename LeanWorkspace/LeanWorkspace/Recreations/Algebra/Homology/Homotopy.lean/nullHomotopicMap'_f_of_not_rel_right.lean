import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap'_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₁ : ∀ l : ι, ¬c.Rel l k₁) (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
    (Homotopy.nullHomotopicMap' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ := by
  simp only [Homotopy.nullHomotopicMap']
  rw [Homotopy.nullHomotopicMap_f_of_not_rel_right r₁₀ hk₁]
  split_ifs
  rfl

