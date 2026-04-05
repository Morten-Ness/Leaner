import Mathlib

variable {F α β γ : Type*}

variable {M ι : Type*} {π : ι → Type*} [∀ i, SMul M (π i)]

theorem smul_set_pi_of_surjective (c : M) (I : Set ι) (s : ∀ i, Set (π i))
    (hsurj : ∀ i ∉ I, Function.Surjective (c • · : π i → π i)) : c • I.pi s = I.pi (c • s) := piMap_image_pi hsurj s

