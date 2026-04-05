import Mathlib

open scoped Pointwise

variable {α ι : Type*}

variable [CommMonoid α]

variable [DecidableEq α]

theorem coe_prod (s : Finset ι) (f : ι → Finset α) :
    ↑(∏ i ∈ s, f i) = ∏ i ∈ s, (f i : Set α) := map_prod (coeMonoidHom : Finset α →* Set α) _ _

omit [DecidableEq α]

