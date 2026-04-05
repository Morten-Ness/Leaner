import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem closure_closure_coe_preimage {s : Set M} : closure (((↑) : closure s → M) ⁻¹' s) = ⊤ := eq_top_iff.2 fun x _ ↦ Subtype.recOn x fun _ hx' ↦
    closure_induction (fun _ h ↦ subset_closure h) (one_mem _) (fun _ _ _ _ ↦ mul_mem) hx'

