import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

variable [EquivLike F M N] [MulEquivClass F M N] (f : F)

theorem MulEquiv.irreducible_iff : Irreducible (f x) ↔ Irreducible x := by
  simp [_root_.irreducible_iff, (EquivLike.surjective f).forall, ← map_mul, -isUnit_map_iff]

