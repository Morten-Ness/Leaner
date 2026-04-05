import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap'_comp (hom : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) (g : D ⟶ E) :
    Homotopy.nullHomotopicMap' hom ≫ g = Homotopy.nullHomotopicMap' fun i j hij => hom i j hij ≫ g.f j := by
  rw [Homotopy.nullHomotopicMap', Homotopy.nullHomotopicMap_comp]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [zero_comp]

