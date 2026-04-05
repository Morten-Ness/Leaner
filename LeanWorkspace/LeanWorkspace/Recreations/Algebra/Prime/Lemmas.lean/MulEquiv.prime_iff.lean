import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M]

variable [CommMonoidWithZero N] {F : Type*} {G : Type*} [FunLike F M N]

variable [MonoidWithZeroHomClass F M N] [FunLike G N M] [MulHomClass G N M]

variable (f : F) (g : G) {p : M}

theorem MulEquiv.prime_iff {E : Type*} [EquivLike E M N] [MulEquivClass E M N] (e : E) :
    Prime (e p) ↔ Prime p := by
  let e := MulEquivClass.toMulEquiv e
  exact ⟨comap_prime e e.symm fun a => by simp,
    fun h => (comap_prime e.symm e fun a => by simp) <| (e.symm_apply_apply p).substr h⟩

