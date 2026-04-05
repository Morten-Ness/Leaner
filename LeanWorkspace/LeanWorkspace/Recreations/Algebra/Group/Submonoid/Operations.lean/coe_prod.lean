import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem coe_prod (s : Submonoid M) (t : Submonoid N) :
    (s.prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) := rfl

