import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem attach_affineCombination_coe (s : Finset P) (w : P → k) :
    s.attach.affineCombination k ((↑) : s → P) (w ∘ (↑)) = s.affineCombination k id w := by
  classical rw [Finset.attach_affineCombination_of_injective s w ((↑) : s → P) Subtype.coe_injective,
      univ_eq_attach, attach_image_val]

