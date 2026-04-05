import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap_f_eq_zero {k₀ : ι} (hk₀ : ∀ l : ι, ¬c.Rel k₀ l)
    (hk₀' : ∀ l : ι, ¬c.Rel l k₀) (hom : ∀ i j, C.X i ⟶ D.X j) :
    (Homotopy.nullHomotopicMap hom).f k₀ = 0 := by
  dsimp [Homotopy.nullHomotopicMap, dNext, prevD]
  rw [C.shape, D.shape, zero_comp, comp_zero, add_zero] <;> apply_assumption

