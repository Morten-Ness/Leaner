import Mathlib

variable {K ι : Type*} {R : ι → Type*}

theorem smul_pi_subset [∀ i, SMul K (R i)] (r : K) (s : Set ι) (t : ∀ i, Set (R i)) :
    r • pi s t ⊆ pi s (r • t) := piMap_image_pi_subset _

