import Mathlib

section

variable {M α : Type*}

theorem AddMonoidHom.mul_op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : αᵐᵒᵖ →+ β)
    (h :
      f.comp (MulOpposite.opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom =
        g.comp (MulOpposite.opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom) :
    f = g := AddMonoidHom.ext <| MulOpposite.rec' fun x => (DFunLike.congr_fun h :) x

end
