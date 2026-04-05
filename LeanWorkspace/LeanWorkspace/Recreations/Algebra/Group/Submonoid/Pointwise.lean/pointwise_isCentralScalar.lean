import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [Monoid α] [MulDistribMulAction α M]

theorem pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α M] :
    IsCentralScalar α (Submonoid M) := ⟨fun _ S => (congr_arg fun f : Monoid.End M => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] Submonoid.pointwise_isCentralScalar

