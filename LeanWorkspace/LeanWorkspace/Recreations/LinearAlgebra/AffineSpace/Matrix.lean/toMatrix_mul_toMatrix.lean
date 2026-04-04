import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

variable {ι' : Type*}

variable [Fintype ι] (b₂ : AffineBasis ι k P)

variable [DecidableEq ι]

theorem toMatrix_mul_toMatrix : b.toMatrix b₂ * b₂.toMatrix b = 1 := by
  ext l m
  change (b.coords (b₂ l) ᵥ* b₂.toMatrix b) m = _
  rw [AffineBasis.toMatrix_vecMul_coords, coords_apply, ← AffineBasis.toMatrix_apply, AffineBasis.toMatrix_self]

