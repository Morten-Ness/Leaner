import Mathlib

section

variable {M : Type*}

variable [AddMonoid M]

theorem AddMonoidHom.apply_nat (f : ℕ →+ M) (n : ℕ) : f n = n • f 1 := by
  rw [← multiplesHom_symm_apply, ← multiplesHom_apply, Equiv.apply_symm_apply]

end

section

variable {M : Type*}

variable [Monoid M]

theorem MonoidHom.apply_mnat (f : Multiplicative ℕ →* M) (n : Multiplicative ℕ) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← powersHom_symm_apply, ← powersHom_apply, Equiv.apply_symm_apply]

end

section

variable {M : Type*}

variable [Monoid M]

theorem MonoidHom.ext_mnat ⦃f g : Multiplicative ℕ →* M⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := MonoidHom.ext fun n ↦ by rw [f.apply_mnat, g.apply_mnat, h]

end

section

variable {M : Type*}

variable {A B F : Type*} [FunLike F ℕ A]

theorem ext_nat' [AddZeroClass A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g := DFunLike.ext f g <| by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]

end
