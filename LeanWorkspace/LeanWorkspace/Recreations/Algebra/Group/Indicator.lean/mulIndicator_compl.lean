import Mathlib

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem mulIndicator_compl (s : Set α) (f : α → G) :
    mulIndicator sᶜ f = f * (mulIndicator s f)⁻¹ := eq_mul_inv_of_mul_eq <| Set.mulIndicator_compl_mul_self s f

