import Mathlib

variable {V : Type*} [Category* V] [Abelian V]

theorem imageToKernel_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.op f.op (by rw [← op_comp, w, op_zero]) =
      (imageSubobjectIso _ ≪≫ (imageOpOp _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).op ≫
          (kernelSubobjectIso _ ≪≫ kernelOpOp _).inv := by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelOpOp_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, ← op_comp, cokernel.π_desc,
    ← imageSubobject_arrow, ← imageUnopOp_inv_comp_op_factorThruImage g.op]
  rfl

