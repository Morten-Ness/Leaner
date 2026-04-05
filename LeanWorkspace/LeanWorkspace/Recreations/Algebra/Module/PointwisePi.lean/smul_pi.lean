import Mathlib

variable {K ι : Type*} {R : ι → Type*}

theorem smul_pi [Group K] [∀ i, MulAction K (R i)] (r : K) (S : Set ι) (t : ∀ i, Set (R i)) :
    r • S.pi t = S.pi (r • t) := piMap_image_pi (fun _ _ => MulAction.surjective _) _

