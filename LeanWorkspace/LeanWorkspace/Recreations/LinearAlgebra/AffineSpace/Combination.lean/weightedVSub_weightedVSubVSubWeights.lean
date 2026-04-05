import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem weightedVSub_weightedVSubVSubWeights [DecidableEq ι] (p : ι → P) {i j : ι} (hi : i ∈ s)
    (hj : j ∈ s) : s.weightedVSub p (Finset.weightedVSubVSubWeights k i j) = p i -ᵥ p j := by
  rw [Finset.weightedVSubVSubWeights, ← Finset.affineCombination_vsub,
    Finset.affineCombination_affineCombinationSingleWeights s k p hi,
    Finset.affineCombination_affineCombinationSingleWeights s k p hj]

