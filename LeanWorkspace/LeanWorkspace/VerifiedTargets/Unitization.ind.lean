import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A → Prop}
    (inl_add_inr : ∀ (r : R) (a : A), P (Unitization.inl r + (a : Unitization R A))) (x) : P x := Unitization.inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.fst x.snd

