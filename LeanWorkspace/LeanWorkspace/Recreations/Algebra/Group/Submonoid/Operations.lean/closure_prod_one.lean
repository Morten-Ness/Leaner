import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem closure_prod_one (s : Set M) : closure (s ×ˢ ({1} : Set N)) = (closure s).prod ⊥ := le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, .rfl⟩)
    (Submonoid.prod_le_iff.2 ⟨
      Submonoid.map_le_of_le_comap _ <| closure_le.2 fun _x hx => subset_closure ⟨hx, rfl⟩, by simp⟩)

