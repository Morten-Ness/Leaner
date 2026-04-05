import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem eqToHom_comp_d {i i' j : ι} (rij : c.Rel i j) (rij' : c.Rel i' j) :
    eqToHom (congr_arg C.X (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j := by
  obtain rfl := c.prev_eq rij rij'
  simp only [eqToHom_refl, id_comp]

