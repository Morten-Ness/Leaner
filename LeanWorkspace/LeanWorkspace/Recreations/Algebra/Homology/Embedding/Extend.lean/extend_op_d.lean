import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

set_option backward.isDefEq.respectTransparency false in
theorem extend_op_d (i' j' : ι') :
    (K.op.extend e.op).d i' j' =
      (K.extendOpIso e).hom.f i' ≫ ((K.extend e).d j' i').op ≫
        (K.extendOpIso e).inv.f j' := by
  have := (K.extendOpIso e).inv.comm i' j'
  dsimp at this
  rw [← this, ← comp_f_assoc, Iso.hom_inv_id, id_f, id_comp]

