import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_const_preimage (U : Set α) (s : Set M) (a : M) :
    (U.mulIndicator fun _ => a) ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := by
  classical
    rw [Set.mulIndicator_const_preimage_eq_union]
    split_ifs <;> simp

