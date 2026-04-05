import Mathlib

variable {α β γ : Type*}

variable {M G : Type*}

variable [AddGroup G]

theorem logEquiv_unitsMk0 (x : Gᵐ⁰) (hx) : WithZero.logEquiv (.mk0 x hx) = WithZero.log x := logEquiv_apply _

