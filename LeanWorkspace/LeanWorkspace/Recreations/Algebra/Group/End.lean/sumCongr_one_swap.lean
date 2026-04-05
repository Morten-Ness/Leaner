import Mathlib

variable {A M G α β γ : Type*}

theorem sumCongr_one_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : β) :
    sumCongr (1 : Equiv.Perm α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := sumCongr_refl_swap i j

