import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mclosure_preimage_le (f : F) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f := closure_le.2 fun _ hx => SetLike.mem_coe.2 <| Submonoid.mem_comap.2 <| subset_closure hx

