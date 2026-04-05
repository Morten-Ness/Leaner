import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

variable (K : HomologicalComplex V c) (i : ι) [K.HasHomology i]

variable (j : ι)

set_option backward.isDefEq.respectTransparency false in
theorem fromOpcycles_op_cyclesOpIso_inv :
    (K.fromOpcycles i j).op ≫ (K.cyclesOpIso i).inv = K.op.toCycles j i := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).fromOpcycles_op_cyclesOpIso_inv
  · rw [K.op.toCycles_eq_zero hij, K.fromOpcycles_eq_zero hij, op_zero, zero_comp]

