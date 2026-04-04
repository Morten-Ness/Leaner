import Mathlib

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Ring k]

variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [DistribSMul M V] [SMulCommClass M k V] {a : M} {s : AffineSubspace k V}
  {p : V}

theorem coe_smul (a : M) (s : AffineSubspace k V) : ↑(a • s) = a • (s : Set V) := rfl

