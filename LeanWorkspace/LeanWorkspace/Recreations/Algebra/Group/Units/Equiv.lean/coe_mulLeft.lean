import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (a * ·) := rfl

