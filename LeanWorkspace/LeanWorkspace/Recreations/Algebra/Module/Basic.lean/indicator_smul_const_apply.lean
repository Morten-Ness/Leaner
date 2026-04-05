import Mathlib

variable {α R M M₂ : Type*}

variable [Zero R] [Zero M] [SMulWithZero R M]

theorem indicator_smul_const_apply (s : Set α) (r : α → R) (m : M) (a : α) :
    indicator s (r · • m) a = indicator s r a • m := Set.indicator_smul_apply_left _ _ _ _

