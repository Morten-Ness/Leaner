import Mathlib

variable {A M G α β γ : Type*}

theorem sumCongr_swap_one {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : α) :
    sumCongr (Equiv.swap i j) (1 : Equiv.Perm β) = Equiv.swap (Sum.inl i) (Sum.inl j) := sumCongr_swap_refl i j

