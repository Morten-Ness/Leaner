import Mathlib

variable {A M G α β γ : Type*}

theorem sumCongr_mul {α β : Type*} (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α) (h : Equiv.Perm β) :
    sumCongr e f * sumCongr g h = sumCongr (e * g) (f * h) := sumCongr_trans g h e f

