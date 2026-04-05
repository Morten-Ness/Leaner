import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem image_eq_image [HasImages V] [HasEqualizers V] {i i' j : ι} (r : c.Rel i j)
    (r' : c.Rel i' j) : imageSubobject (C.d i j) = imageSubobject (C.d i' j) := by
  rw [← HomologicalComplex.eqToHom_comp_d C r r']
  apply imageSubobject_iso_comp

