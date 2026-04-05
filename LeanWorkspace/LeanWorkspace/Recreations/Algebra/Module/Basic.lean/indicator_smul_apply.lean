import Mathlib

variable {α R M M₂ : Type*}

variable [Zero M] [SMulZeroClass R M]

theorem indicator_smul_apply (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = r a • indicator s f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r a)).symm]

