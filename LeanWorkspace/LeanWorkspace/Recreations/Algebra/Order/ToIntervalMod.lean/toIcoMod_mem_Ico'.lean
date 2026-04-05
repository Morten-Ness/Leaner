import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_mem_Ico' (b : α) : toIcoMod hp 0 b ∈ Set.Ico 0 p := by
  convert toIcoMod_mem_Ico hp 0 b
  exact (zero_add p).symm

