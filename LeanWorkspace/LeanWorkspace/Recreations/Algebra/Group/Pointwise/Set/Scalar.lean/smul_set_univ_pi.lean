import Mathlib

variable {F α β γ : Type*}

variable {M ι : Type*} {π : ι → Type*} [∀ i, SMul M (π i)]

theorem smul_set_univ_pi (c : M) (s : ∀ i, Set (π i)) : c • univ.pi s = univ.pi (c • s) := piMap_image_univ_pi _ s

