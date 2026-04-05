import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.prod {M : Type*} [CommMonoid M] {ι : Type*} {f : ι → α → M}
    (hf : ∀ i, HasFiniteMulSupport (f i)) (s : Finset ι) :
    HasFiniteMulSupport fun a ↦ ∏ i ∈ s, f i a := (s.finite_toSet.biUnion fun i _ ↦ hf i).subset <| s.mulSupport_prod f

