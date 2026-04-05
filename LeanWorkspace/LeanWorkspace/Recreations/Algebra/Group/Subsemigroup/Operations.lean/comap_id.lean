import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_id (S : Subsemigroup P) : S.comap (MulHom.id _) = S := ext (by simp)

