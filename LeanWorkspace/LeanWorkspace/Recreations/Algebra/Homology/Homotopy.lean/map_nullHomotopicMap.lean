import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

set_option backward.isDefEq.respectTransparency false in
theorem map_nullHomotopicMap {W : Type*} [Category* W] [Preadditive W] (G : V ⥤ W) [G.Additive]
    (hom : ∀ i j, C.X i ⟶ D.X j) :
    (G.mapHomologicalComplex c).map (Homotopy.nullHomotopicMap hom) =
      Homotopy.nullHomotopicMap (fun i j => by exact G.map (hom i j)) := by
  ext i
  dsimp [Homotopy.nullHomotopicMap, dNext, prevD]
  simp only [G.map_comp, Functor.map_add]

