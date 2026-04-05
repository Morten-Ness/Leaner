import Mathlib

variable {ι F M N O G H : Type*}

variable [Zero M] [Zero N] [Zero O]

theorem apply_single [FunLike F M N] [ZeroHomClass F M N] (e : F) (i : ι) (m : M) (b : ι) :
    e (single i m b) = single i (e m) b := apply_single' e (map_zero e) i m b

