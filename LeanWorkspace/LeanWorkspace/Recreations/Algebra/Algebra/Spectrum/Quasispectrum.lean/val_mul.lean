import Mathlib

variable {R : Type*} [NonUnitalSemiring R]

theorem val_mul (x y : PreQuasiregular R) : (x * y).val = y.val + x.val + x.val * y.val := rfl

