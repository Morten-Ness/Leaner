import Mathlib

section

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Field k] [AddCommGroup V] [Module k V] {a : k}

theorem direction_smul (ha : a ≠ 0) (s : AffineSubspace k V) : (a • s).direction = s.direction := by
  have : DistribSMul.toLinearMap k V a = a • LinearMap.id := by
    ext; simp
  simp [AffineSubspace.smul_eq_map, map_direction, this, Submodule.map_smul, ha]

end

section

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Ring k]

variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem map_pointwise_vadd (f : P₁ →ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
    (v +ᵥ s).map f = f.linear v +ᵥ s.map f := by
  rw [AffineSubspace.pointwise_vadd_eq_map, AffineSubspace.pointwise_vadd_eq_map, map_map, map_map]
  congr 1
  ext
  exact f.map_vadd _ _

end

section

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Ring k]

variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem pointwise_vadd_direction (v : V) (s : AffineSubspace k P) :
    (v +ᵥ s).direction = s.direction := by
  rw [AffineSubspace.pointwise_vadd_eq_map, map_direction]
  exact Submodule.map_id _

end

section

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Ring k]

variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [Monoid M] [DistribMulAction M V] [SMulCommClass M k V] {a : M} {s : AffineSubspace k V}
  {p : V}

theorem smul_mem_smul_iff_of_isUnit (ha : IsUnit a) : a • p ∈ a • s ↔ p ∈ s := AffineSubspace.smul_mem_smul_iff (a := ha.unit)

end

section

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Ring k]

variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [Monoid M] [DistribMulAction M V] [SMulCommClass M k V] {a : M} {s : AffineSubspace k V}
  {p : V}

theorem smul_mem_smul_iff₀ {G₀ : Type*} [GroupWithZero G₀] [DistribMulAction G₀ V]
    [SMulCommClass G₀ k V] {a : G₀} (ha : a ≠ 0) : a • p ∈ a • s ↔ p ∈ s := AffineSubspace.smul_mem_smul_iff_of_isUnit ha.isUnit

end
