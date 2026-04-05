import Mathlib

variable {G H I : Type*}

variable [Monoid G] [Monoid H] [Monoid I]

theorem mgraph_eq_mrange_prod (f : G →* H) : f.mgraph = mrange ((id _).prod f) := by aesop

