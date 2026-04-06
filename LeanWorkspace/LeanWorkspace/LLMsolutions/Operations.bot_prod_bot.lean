import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥ := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx1, hx2⟩
    have hx1' : x.1 = 1 := by simpa using hx1
    have hx2' : x.2 = 1 := by simpa using hx2
    ext <;> assumption
  · intro hx
    have hx' : x = (1, 1) := by simpa using hx
    rw [hx']
    constructor <;> simp
