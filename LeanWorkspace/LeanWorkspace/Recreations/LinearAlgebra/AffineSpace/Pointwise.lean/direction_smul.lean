import Mathlib

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Field k] [AddCommGroup V] [Module k V] {a : k}

theorem direction_smul (ha : a ≠ 0) (s : AffineSubspace k V) : (a • s).direction = s.direction := by
  have : DistribSMul.toLinearMap k V a = a • LinearMap.id := by
    ext; simp
  simp [AffineSubspace.smul_eq_map, map_direction, this, Submodule.map_smul, ha]

