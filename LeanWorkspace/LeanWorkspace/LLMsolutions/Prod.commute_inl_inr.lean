import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem commute_inl_inr (m : M) (n : N) : Commute (MonoidHom.inl M N m) (MonoidHom.inr M N n) := by
  show (m, 1) * (1, n) = (1, n) * (m, 1)
  simp [Prod.fst_mul, Prod.snd_mul]
