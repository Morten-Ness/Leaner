import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap_f {k₂ k₁ k₀ : ι} (r₂₁ : c.Rel k₂ k₁) (r₁₀ : c.Rel k₁ k₀)
    (hom : ∀ i j, C.X i ⟶ D.X j) :
    (Homotopy.nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ + hom k₁ k₂ ≫ D.d k₂ k₁ := by
  dsimp only [Homotopy.nullHomotopicMap]
  rw [dNext_eq hom r₁₀, prevD_eq hom r₂₁]

-- Cannot be @[simp] because `k₀` and `k₂` cannot be inferred by `simp`.

