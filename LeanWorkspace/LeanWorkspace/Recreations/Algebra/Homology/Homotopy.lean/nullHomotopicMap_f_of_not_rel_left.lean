import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.Rel k₁ k₀)
    (hk₀ : ∀ l : ι, ¬c.Rel k₀ l) (hom : ∀ i j, C.X i ⟶ D.X j) :
    (Homotopy.nullHomotopicMap hom).f k₀ = hom k₀ k₁ ≫ D.d k₁ k₀ := by
  dsimp only [Homotopy.nullHomotopicMap]
  rw [prevD_eq hom r₁₀, dNext, AddMonoidHom.mk'_apply, C.shape, zero_comp, zero_add]
  exact hk₀ _

-- Cannot be @[simp] because `k₁` cannot be inferred by `simp`.

