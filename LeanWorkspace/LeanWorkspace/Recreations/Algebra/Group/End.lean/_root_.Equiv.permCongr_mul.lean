import Mathlib

variable {A M G α β γ : Type*}

theorem _root_.Equiv.permCongr_mul (e : α ≃ β) (p q : Equiv.Perm α) :
    e.permCongr (p * q) = e.permCongr p * e.permCongr q := permCongr_trans e q p |>.symm

