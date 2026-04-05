import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

set_option backward.isDefEq.respectTransparency false in
theorem map_nullHomotopicMap' {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    (hom : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
    (G.mapHomologicalComplex c).map (Homotopy.nullHomotopicMap' hom) =
      Homotopy.nullHomotopicMap' fun i j hij => by exact G.map (hom i j hij) := by
  rw [Homotopy.nullHomotopicMap', Homotopy.map_nullHomotopicMap]
  congr
  ext i j
  split_ifs
  · rfl
  · rw [G.map_zero]

