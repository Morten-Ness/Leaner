import Mathlib

section

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

theorem commute_inl_inr (m : M) (n : N) : Commute (MonoidHom.inl M N m) (MonoidHom.inr M N n) := Commute.prod (.one_right m) (.one_left n)

end

section

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

theorem embedProduct_injective (α : Type*) [Monoid α] : Function.Injective (Units.embedProduct α) := fun _ _ h => Units.ext <| (congr_arg Prod.fst h :)

end

section

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1, p.snd) = p := Prod.ext (mul_one p.1) (one_mul p.2)

end
