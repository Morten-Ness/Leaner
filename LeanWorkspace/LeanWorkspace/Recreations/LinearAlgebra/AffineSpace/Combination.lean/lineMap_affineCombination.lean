import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

variable {k V}

theorem lineMap_affineCombination (w₁ : ι → k) (w₂ : ι → k) (r : k) (p : ι → P) :
    AffineMap.lineMap (s.affineCombination k p w₁) (s.affineCombination k p w₂) r =
    s.affineCombination k p (AffineMap.lineMap w₁ w₂ r) := by
  simp_rw [Finset.affineCombination_apply, ← AffineMap.lineMap_vadd, AffineMap.lineMap_apply_module,
    map_add, map_smul]

