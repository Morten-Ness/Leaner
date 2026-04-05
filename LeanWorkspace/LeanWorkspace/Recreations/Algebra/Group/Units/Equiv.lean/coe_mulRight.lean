import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a := rfl

