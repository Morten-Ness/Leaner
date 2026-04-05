import Mathlib

variable {α R M M₂ : Type*}

variable [Zero R] [Zero M] [SMulWithZero R M]

theorem indicator_smul_apply_left (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = indicator s r a • f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (zero_smul _ (f a)).symm]

