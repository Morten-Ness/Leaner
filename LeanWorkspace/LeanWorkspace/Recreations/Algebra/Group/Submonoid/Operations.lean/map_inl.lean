import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem map_inl (s : Submonoid M) : s.map (inl M N) = s.prod ⊥ := ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
      ⟨p.1, hps, Prod.ext rfl <| (Set.eq_of_mem_singleton hp1).symm⟩⟩

