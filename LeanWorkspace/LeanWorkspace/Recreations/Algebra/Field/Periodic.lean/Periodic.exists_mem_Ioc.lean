import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.exists_mem_Ioc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ioc a (a + c), f x = f y := let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

