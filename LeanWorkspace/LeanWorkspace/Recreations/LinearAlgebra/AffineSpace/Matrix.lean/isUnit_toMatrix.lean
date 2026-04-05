import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

variable {ι' : Type*}

variable [Fintype ι] (b₂ : AffineBasis ι k P)

variable [DecidableEq ι]

theorem isUnit_toMatrix : IsUnit (b.toMatrix b₂) := ⟨{  val := b.toMatrix b₂
      inv := b₂.toMatrix b
      val_inv := AffineBasis.toMatrix_mul_toMatrix b b₂
      inv_val := AffineBasis.toMatrix_mul_toMatrix b₂ b }, rfl⟩

