import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_preimage_of_notMem (s : Set α) (f : α → M) {t : Set M} (ht : (1 : M) ∉ t) :
    Set.mulIndicator s f ⁻¹' t = f ⁻¹' t ∩ s := by
  simp [Set.mulIndicator_preimage, Pi.one_def, Set.preimage_const_of_notMem ht]

