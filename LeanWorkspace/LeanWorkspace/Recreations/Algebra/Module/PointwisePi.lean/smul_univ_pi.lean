import Mathlib

variable {K ι : Type*} {R : ι → Type*}

theorem smul_univ_pi [∀ i, SMul K (R i)] (r : K) (t : ∀ i, Set (R i)) :
    r • pi (Set.univ : Set ι) t = pi (Set.univ : Set ι) (r • t) := piMap_image_univ_pi _ _

