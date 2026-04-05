import Mathlib

variable {F α M N G : Type*}

variable [Monoid M] [Monoid N]

theorem coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (Units.mapEquiv h x : N) = h x := rfl

