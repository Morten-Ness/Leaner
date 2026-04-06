FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    {x ∈ s | pred x}.affineCombination k p w = s.affineCombination k p w := by
  classical
  refine Finset.affineCombination_eq_of_eq_weights ?_
  intro i hi
  by_cases hp : pred i
  · simp [Finset.mem_filter] at hi
    exact hi.1
  · exfalso
    exact hp (h i hi.1 hi.2)
