import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).affineCombination k (fun i => p i) fun i => w i) =
      {x ∈ s | pred x}.affineCombination k p w := by
  rw [Finset.affineCombination_subtype_eq_filter]
