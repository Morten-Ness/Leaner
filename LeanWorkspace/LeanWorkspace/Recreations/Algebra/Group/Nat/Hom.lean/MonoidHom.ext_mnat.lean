import Mathlib

variable {M : Type*}

variable [Monoid M]

theorem MonoidHom.ext_mnat ⦃f g : Multiplicative ℕ →* M⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := MonoidHom.ext fun n ↦ by rw [f.apply_mnat, g.apply_mnat, h]

