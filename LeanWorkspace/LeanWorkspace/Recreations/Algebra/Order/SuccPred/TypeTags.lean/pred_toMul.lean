import Mathlib

variable {X : Type*}

theorem pred_toMul [Preorder X] [PredOrder X] (x : Additive X) : pred x.toMul = (pred x).toMul := rfl

