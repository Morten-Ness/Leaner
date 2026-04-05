import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap_comp (hom : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) :
    Homotopy.nullHomotopicMap hom ≫ g = Homotopy.nullHomotopicMap fun i j => hom i j ≫ g.f j := by
  ext n
  dsimp [Homotopy.nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.add_comp, assoc, g.comm]

