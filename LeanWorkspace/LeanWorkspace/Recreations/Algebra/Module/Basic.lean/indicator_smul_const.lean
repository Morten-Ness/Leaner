import Mathlib

variable {α R M M₂ : Type*}

variable [Zero R] [Zero M] [SMulWithZero R M]

theorem indicator_smul_const (s : Set α) (r : α → R) (m : M) :
    indicator s (r · • m) = (indicator s r · • m) := funext <| Set.indicator_smul_const_apply _ _ _

