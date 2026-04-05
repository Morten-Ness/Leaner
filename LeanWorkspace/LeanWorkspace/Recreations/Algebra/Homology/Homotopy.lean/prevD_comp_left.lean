import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem prevD_comp_left (f : C ⟶ D) (g : ∀ i j, D.X i ⟶ E.X j) (j : ι) :
    (prevD j fun i j => f.f i ≫ g i j) = f.f j ≫ prevD j g := assoc _ _ _

-- This is not a simp lemma; the LHS already simplifies.

