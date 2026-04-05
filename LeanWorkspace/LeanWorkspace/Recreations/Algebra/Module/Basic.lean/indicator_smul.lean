import Mathlib

variable {α R M M₂ : Type*}

variable [Zero M] [SMulZeroClass R M]

theorem indicator_smul (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ r a • indicator s f a := funext <| Set.indicator_smul_apply s r f

