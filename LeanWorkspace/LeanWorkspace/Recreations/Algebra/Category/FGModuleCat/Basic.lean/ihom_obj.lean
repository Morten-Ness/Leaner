import Mathlib

variable (K : Type u) [Field K]

variable (V W : FGModuleCat K)

theorem ihom_obj : (ihom V).obj W = FGModuleCat.of K (V.obj ⟶ W.obj) := rfl

