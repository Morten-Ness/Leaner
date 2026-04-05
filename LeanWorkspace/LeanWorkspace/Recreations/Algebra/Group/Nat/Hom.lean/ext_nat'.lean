import Mathlib

variable {M : Type*}

variable {A B F : Type*} [FunLike F ℕ A]

theorem ext_nat' [AddZeroClass A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g := DFunLike.ext f g <| by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]

