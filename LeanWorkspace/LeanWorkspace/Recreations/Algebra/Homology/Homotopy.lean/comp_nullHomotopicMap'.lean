import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem comp_nullHomotopicMap' (f : C ⟶ D) (hom : ∀ i j, c.Rel j i → (D.X i ⟶ E.X j)) :
    f ≫ Homotopy.nullHomotopicMap' hom = Homotopy.nullHomotopicMap' fun i j hij => f.f i ≫ hom i j hij := by
  rw [Homotopy.nullHomotopicMap', Homotopy.comp_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [comp_zero]

