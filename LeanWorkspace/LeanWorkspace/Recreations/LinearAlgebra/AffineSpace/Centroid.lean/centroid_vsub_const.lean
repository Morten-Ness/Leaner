import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem centroid_vsub_const [CharZero k] {p : ι → P} {p₀ : P} (hs : s.Nonempty) :
    Finset.centroid k s p -ᵥ p₀ = Finset.centroid k s (fun i => p i -ᵥ p₀) := by
  have h := s.sum_centroidWeights_eq_one_of_nonempty k hs
  simp only [Finset.centroid_def]
  grind [sum_smul_vsub_const_eq_affineCombination_vsub, affineCombination_eq_linear_combination]

