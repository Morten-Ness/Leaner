import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem QuotientAddGroup.equivIocMod_zero (a : α) :
    QuotientAddGroup.equivIocMod hp a 0 = ⟨toIocMod hp a 0, toIocMod_mem_Ioc hp a _⟩ := rfl

