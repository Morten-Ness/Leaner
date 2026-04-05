import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.prodMk {M' : Type*} [One M'] {f : α → M} {g : α → M'}
    (hf : HasFiniteMulSupport f) (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ (f a, g a) := by
  simp only [HasFiniteMulSupport] at hf hg ⊢
  rw [mulSupport_prodMk f g]
  exact hf.union hg

