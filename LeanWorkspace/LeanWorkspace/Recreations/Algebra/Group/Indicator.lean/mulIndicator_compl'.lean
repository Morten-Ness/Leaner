import Mathlib

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem mulIndicator_compl' (s : Set α) (f : α → G) :
    mulIndicator sᶜ f = f / mulIndicator s f := by rw [div_eq_mul_inv, Set.mulIndicator_compl]

