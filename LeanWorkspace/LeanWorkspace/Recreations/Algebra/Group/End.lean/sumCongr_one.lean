import Mathlib

variable {A M G α β γ : Type*}

theorem sumCongr_one {α β : Type*} : sumCongr (1 : Equiv.Perm α) (1 : Equiv.Perm β) = 1 := sumCongr_refl

