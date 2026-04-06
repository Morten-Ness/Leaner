import Mathlib

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem coe_prod (s : Finset ι) (ψ : ι → AddChar A M) : ∏ i ∈ s, ψ i = ∏ i ∈ s, ⇑(ψ i) := by
  ext a
  simp
