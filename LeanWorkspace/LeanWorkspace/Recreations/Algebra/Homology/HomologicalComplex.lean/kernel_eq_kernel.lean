import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem kernel_eq_kernel [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i j') :
    kernelSubobject (C.d i j) = kernelSubobject (C.d i j') := by
  rw [← HomologicalComplex.d_comp_eqToHom C r r']
  apply kernelSubobject_comp_mono

