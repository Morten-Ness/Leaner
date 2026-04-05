import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

theorem cancel_right {g₁ g₂ f : CentroidHom α} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := ⟨fun h ↦ CentroidHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun a ↦ congrFun (congrArg CentroidHom.comp a) f⟩

