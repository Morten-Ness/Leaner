import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem smul_set_pi {G ι : Type*} {α : ι → Type*} [Group G] [∀ i, MulAction G (α i)]
    (c : G) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := smul_set_pi_of_surjective c I s fun _ _ ↦ (MulAction.bijective c).surjective

