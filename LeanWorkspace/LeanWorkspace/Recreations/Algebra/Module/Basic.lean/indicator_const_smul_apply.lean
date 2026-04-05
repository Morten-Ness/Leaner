import Mathlib

variable {α R M M₂ : Type*}

variable [Zero M] [SMulZeroClass R M]

theorem indicator_const_smul_apply (s : Set α) (r : R) (f : α → M) (a : α) :
    indicator s (r • f ·) a = r • indicator s f a := Set.indicator_smul_apply s (fun _ ↦ r) f a

