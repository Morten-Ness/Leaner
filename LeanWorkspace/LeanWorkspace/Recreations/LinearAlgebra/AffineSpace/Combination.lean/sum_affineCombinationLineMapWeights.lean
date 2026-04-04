import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem sum_affineCombinationLineMapWeights [DecidableEq ι] {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (c : k) : ∑ t ∈ s, Finset.affineCombinationLineMapWeights i j c t = 1 := by
  simp_rw [Finset.affineCombinationLineMapWeights, Pi.add_apply, sum_add_distrib]
  simp [hi, hj, ← mul_sum]

