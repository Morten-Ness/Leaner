import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

variable (K : HomologicalComplex V c) (i : ι) [K.HasHomology i]

variable (j : ι)

set_option backward.isDefEq.respectTransparency false in
theorem opcyclesOpIso_hom_toCycles_op :
    (K.opcyclesOpIso i).hom ≫ (K.toCycles j i).op = K.op.fromOpcycles i j := by
  by_cases hij : c.Rel j i
  · obtain rfl := c.prev_eq' hij
    exact (K.sc i).opcyclesOpIso_hom_toCycles_op
  · rw [K.toCycles_eq_zero hij, K.op.fromOpcycles_eq_zero hij, op_zero, comp_zero]

