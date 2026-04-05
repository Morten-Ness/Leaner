import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {F : Type*}

variable [FunLike F A B] [AlgHomClass F R A B]

theorem ext_on_codisjoint {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T)
    (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) : φ = ψ := DFunLike.ext _ _ fun _ ↦ AlgHom.eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

