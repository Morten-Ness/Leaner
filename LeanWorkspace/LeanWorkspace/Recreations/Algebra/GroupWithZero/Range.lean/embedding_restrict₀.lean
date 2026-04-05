import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem embedding_restrict₀ (a : A) : MonoidWithZeroHom.ValueGroup₀.embedding (restrict₀ f a) = f a := by
  simp only [restrict₀_apply, embedding_apply]
  aesop

