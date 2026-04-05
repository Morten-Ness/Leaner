import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem prevD_comp_right (f : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι) :
    (prevD j fun i j => f i j ≫ g.f j) = prevD j f ≫ g.f j := by
  dsimp [prevD]
  simp only [assoc, g.comm]

