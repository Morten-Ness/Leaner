import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem ind {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M → Prop}
    (inl_add_inr : ∀ r m, P (TrivSqZeroExt.inl r + TrivSqZeroExt.inr m)) (x) : P x := TrivSqZeroExt.inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.1 x.2

