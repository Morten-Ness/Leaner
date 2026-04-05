import Mathlib

variable {R : Type*}

variable [MulOneClass R]

theorem isRegular_one : IsRegular (1 : R) := ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩

