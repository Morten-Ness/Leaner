import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem map_affineCombination {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    (p : ι → P) (w : ι → k) (hw : s.sum w = 1) (f : P →ᵃ[k] P₂) :
    f (s.affineCombination k p w) = s.affineCombination k (f ∘ p) w := by
  have b := Classical.choice (inferInstance : AddTorsor V P).nonempty
  have b₂ := Classical.choice (inferInstance : AddTorsor V₂ P₂).nonempty
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one s w p hw b,
    Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one s w (f ∘ p) hw b₂, ←
    Finset.weightedVSubOfPoint_vadd_eq_of_sum_eq_one s w (f ∘ p) hw (f b) b₂]
  simp only [Finset.weightedVSubOfPoint_apply, RingHom.id_apply, AffineMap.map_vadd, map_smulₛₗ,
    AffineMap.linearMap_vsub, map_sum, Function.comp_apply]

