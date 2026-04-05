import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem closure_one_prod (t : Set N) : closure (({1} : Set M) ×ˢ t) = .prod ⊥ (closure t) := le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨.rfl, subset_closure⟩)
    (Submonoid.prod_le_iff.2 ⟨by simp,
      Submonoid.map_le_of_le_comap _ <| closure_le.2 fun _y hy => subset_closure ⟨rfl, hy⟩⟩)

