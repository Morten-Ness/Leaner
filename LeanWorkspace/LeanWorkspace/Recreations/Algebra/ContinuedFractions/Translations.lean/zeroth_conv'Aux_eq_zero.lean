import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem zeroth_conv'Aux_eq_zero {s : Stream'.Seq <| Pair K} :
    convs'Aux s 0 = (0 : K) := rfl

