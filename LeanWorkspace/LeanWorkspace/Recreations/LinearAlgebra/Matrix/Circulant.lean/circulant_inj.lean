import Mathlib

variable {α β n R : Type*}

theorem circulant_inj [SubtractionMonoid n] {v w : n → α} : Matrix.circulant v = Matrix.circulant w ↔ v = w := Matrix.circulant_injective.eq_iff

