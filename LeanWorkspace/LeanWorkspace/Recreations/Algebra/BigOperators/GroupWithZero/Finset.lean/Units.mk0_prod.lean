import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

theorem Units.mk0_prod [CommGroupWithZero G₀] (s : Finset ι) (f : ι → G₀) (h) :
    Units.mk0 (∏ i ∈ s, f i) h =
      ∏ i ∈ s.attach, Units.mk0 (f i) fun hh ↦ h (Finset.prod_eq_zero i.2 hh) := by
  induction s using Finset.cons_induction_on <;> simp [*]

