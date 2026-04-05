import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap'_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₀ : ∀ l : ι, ¬c.Rel k₀ l) (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
    (Homotopy.nullHomotopicMap' h).f k₀ = h k₀ k₁ r₁₀ ≫ D.d k₁ k₀ := by
  simp only [Homotopy.nullHomotopicMap']
  rw [Homotopy.nullHomotopicMap_f_of_not_rel_left r₁₀ hk₀]
  split_ifs
  rfl

-- Cannot be @[simp] because `k₀` cannot be inferred by `simp`.

