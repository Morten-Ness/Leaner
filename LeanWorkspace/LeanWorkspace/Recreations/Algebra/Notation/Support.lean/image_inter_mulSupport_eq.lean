import Mathlib

variable {ι κ M N P : Type*}

variable [One M] {f : ι → M} {s : Set κ} {g : κ → ι}

theorem image_inter_mulSupport_eq : g '' s ∩ Function.mulSupport f = g '' (s ∩ Function.mulSupport (f ∘ g)) := by
  rw [Function.mulSupport_comp_eq_preimage f g, image_inter_preimage]

