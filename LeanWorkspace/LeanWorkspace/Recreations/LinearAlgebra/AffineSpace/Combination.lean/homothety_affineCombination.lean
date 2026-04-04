import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem homothety_affineCombination {k V P : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → P) (w : ι → k) {i : ι}
    (hi : i ∈ s) (r : k) :
    AffineMap.homothety (p i) r (s.affineCombination k p w) = s.affineCombination k p
      (AffineMap.lineMap (Finset.affineCombinationSingleWeights k i) w r) := by
  rw [AffineMap.homothety_eq_lineMap, ← Finset.lineMap_affineCombination,
    Finset.affineCombination_affineCombinationSingleWeights _ _ _ hi]

