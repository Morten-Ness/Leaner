import Mathlib

section

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem mem_smul_pointwise_iff_exists (a : A) (m : M) (S : AddSubmonoid A) :
    a ∈ m • S ↔ ∃ s : A, s ∈ S ∧ m • s = a := (Set.mem_smul_set : a ∈ m • (S : Set A) ↔ _)

end

section

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] :
    IsCentralScalar M (AddSubmonoid A) := ⟨fun _ S =>
    (congr_arg fun f : AddMonoid.End A => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwise_isCentralScalar

end

section

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [DistribMulAction M A]

theorem smul_mem_pointwise_smul (a : A) (m : M) (S : AddSubmonoid A) : a ∈ S → m • a ∈ m • S := (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))

end
