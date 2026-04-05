import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_set_coe (s : Set ι) [Fintype s] : (∏ i : s, f i) = ∏ i ∈ s.toFinset, f i := (Finset.prod_subtype s.toFinset (fun _ ↦ Set.mem_toFinset) f).symm

