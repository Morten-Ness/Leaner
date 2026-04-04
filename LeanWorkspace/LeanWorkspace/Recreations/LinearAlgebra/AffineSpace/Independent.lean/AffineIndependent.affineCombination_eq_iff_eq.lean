import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.affineCombination_eq_iff_eq {p : ι → P} (ha : AffineIndependent k p)
    {w₁ w₂ : ι → k} {s : Finset ι} (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1) :
    s.affineCombination k p w₁ = s.affineCombination k p w₂ ↔ ∀ i ∈ s, w₁ i = w₂ i := by
  refine ⟨fun h ↦ ?_, fun h ↦ s.affineCombination_congr h fun _ _ ↦ rfl⟩
  have hi := ha.indicator_eq_of_affineCombination_eq _ _ _ _ hw₁ hw₂ h
  intro i hs
  suffices Set.indicator s w₁ i = Set.indicator s w₂ i by simpa [hs] using this
  simp [hi]

