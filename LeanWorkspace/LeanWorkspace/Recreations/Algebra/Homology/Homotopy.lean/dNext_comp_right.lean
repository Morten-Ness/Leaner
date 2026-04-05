import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem dNext_comp_right (f : ∀ i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι) :
    (dNext i fun i j => f i j ≫ g.f j) = dNext i f ≫ g.f i := (assoc _ _ _).symm

