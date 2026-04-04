import Mathlib

theorem AffineMap.lineMap_mem {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P} (c : k) (h₀ : p₀ ∈ Q) (h₁ : p₁ ∈ Q) :
    AffineMap.lineMap p₀ p₁ c ∈ Q := by
  rw [AffineMap.lineMap_apply]
  exact Q.smul_vsub_vadd_mem c h₁ h₀ h₀

