import Mathlib

variable {α β n R : Type*}

theorem circulant_smul [Sub n] [SMul R α] (k : R) (v : n → α) :
    Matrix.circulant (k • v) = k • Matrix.circulant v := rfl

