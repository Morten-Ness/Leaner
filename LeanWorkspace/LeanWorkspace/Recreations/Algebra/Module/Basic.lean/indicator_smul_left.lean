import Mathlib

variable {α R M M₂ : Type*}

variable [Zero R] [Zero M] [SMulWithZero R M]

theorem indicator_smul_left (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ indicator s r a • f a := funext <| Set.indicator_smul_apply_left _ _ _

