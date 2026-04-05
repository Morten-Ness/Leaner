import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem QuotientAddGroup.equivIocMod_coe (a b : α) :
    QuotientAddGroup.equivIocMod hp a ↑b = ⟨toIocMod hp a b, toIocMod_mem_Ioc hp a _⟩ := rfl

