import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₁ : ∀ l : ι, ¬c.Rel l k₁) (hom : ∀ i j, C.X i ⟶ D.X j) :
    (Homotopy.nullHomotopicMap hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ := by
  dsimp only [Homotopy.nullHomotopicMap]
  rw [dNext_eq hom r₁₀, prevD, AddMonoidHom.mk'_apply, D.shape, comp_zero, add_zero]
  exact hk₁ _

-- Cannot be @[simp] because `k₀` cannot be inferred by `simp`.

