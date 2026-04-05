import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem dNext_comp_left (f : C ⟶ D) (g : ∀ i j, D.X i ⟶ E.X j) (i : ι) :
    (dNext i fun i j => f.f i ≫ g i j) = f.f i ≫ dNext i g := (f.comm_assoc _ _ _).symm

-- This is not a simp lemma; the LHS already simplifies.

