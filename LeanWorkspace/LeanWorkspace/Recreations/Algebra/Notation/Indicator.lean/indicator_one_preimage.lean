import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem indicator_one_preimage [Zero M] (U : Set α) (s : Set M) :
    U.indicator 1 ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := indicator_const_preimage _ _ 1

