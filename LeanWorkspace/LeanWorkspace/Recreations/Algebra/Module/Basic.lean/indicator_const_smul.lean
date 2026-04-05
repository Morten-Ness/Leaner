import Mathlib

variable {α R M M₂ : Type*}

variable [Zero M] [SMulZeroClass R M]

theorem indicator_const_smul (s : Set α) (r : R) (f : α → M) :
    indicator s (r • f ·) = (r • indicator s f ·) := funext <| Set.indicator_const_smul_apply s r f

