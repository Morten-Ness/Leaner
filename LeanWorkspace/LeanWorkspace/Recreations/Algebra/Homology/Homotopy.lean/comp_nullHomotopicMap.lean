import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem comp_nullHomotopicMap (f : C ⟶ D) (hom : ∀ i j, D.X i ⟶ E.X j) :
    f ≫ Homotopy.nullHomotopicMap hom = Homotopy.nullHomotopicMap fun i j => f.f i ≫ hom i j := by
  ext n
  dsimp [Homotopy.nullHomotopicMap, fromNext, toPrev, AddMonoidHom.mk'_apply]
  simp only [Preadditive.comp_add, assoc, f.comm_assoc]

