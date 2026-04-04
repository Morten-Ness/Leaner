import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem affineCombination_affineCombinationLineMapWeights [DecidableEq ι] (p : ι → P) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (c : k) :
    s.affineCombination k p (Finset.affineCombinationLineMapWeights i j c) =
      AffineMap.lineMap (p i) (p j) c := by
  rw [Finset.affineCombinationLineMapWeights, ← Finset.weightedVSub_vadd_affineCombination,
    Finset.weightedVSub_const_smul, s.affineCombination_affineCombinationSingleWeights k p hi,
    s.weightedVSub_weightedVSubVSubWeights k p hj hi, AffineMap.lineMap_apply]

