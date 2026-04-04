import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_eq_iff [CharZero k] {n : ℕ} (s : Affine.Simplex k P n) {fs₁ fs₂ : Finset (Fin (n + 1))}
    {m₁ m₂ : ℕ} (h₁ : #fs₁ = m₁ + 1) (h₂ : #fs₂ = m₂ + 1) :
    fs₁.centroid k s.points = fs₂.centroid k s.points ↔ fs₁ = fs₂ := by
  refine ⟨fun h => ?_, @congrArg _ _ fs₁ fs₂ (fun z => Finset.centroid k z s.points)⟩
  rw [Finset.centroid_eq_affineCombination_fintype,
    Finset.centroid_eq_affineCombination_fintype] at h
  have ha :=
    (affineIndependent_iff_indicator_eq_of_affineCombination_eq k s.points).1 s.independent _ _ _ _
      (fs₁.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one k h₁)
      (fs₂.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one k h₂) h
  simp_rw [Finset.coe_univ, Set.indicator_univ, funext_iff,
    Finset.centroidWeightsIndicator_def, Finset.centroidWeights, h₁, h₂] at ha
  ext i
  specialize ha i
  have key : ∀ n : ℕ, (n : k) + 1 ≠ 0 := fun n h => by norm_cast at h
  -- we should be able to golf this to
  -- `refine ⟨fun hi ↦ decidable.by_contradiction (fun hni ↦ ?_), ...⟩`,
  -- but for some unknown reason it doesn't work.
  constructor <;> intro hi <;> by_contra hni
  · simp [hni, hi, key] at ha
  · simpa [hni, hi, key] using ha.symm

