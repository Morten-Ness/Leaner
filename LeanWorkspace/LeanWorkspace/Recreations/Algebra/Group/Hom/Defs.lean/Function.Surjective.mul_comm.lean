import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem Function.Surjective.mul_comm [Mul M] [Mul N] {f : M →ₙ* N}
    (is_surj : Function.Surjective f) (is_comm : Std.Commutative (· * · : M → M → M)) :
    Std.Commutative (· * · : N → N → N) where
  comm := fun a b ↦ by
    obtain ⟨a', ha'⟩ := is_surj a
    obtain ⟨b', hb'⟩ := is_surj b
    simp only [← ha', ← hb', ← map_mul]
    rw [is_comm.comm]

