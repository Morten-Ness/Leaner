import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem monotone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Monotone f ↔ MonotoneOn f (Icc l (l + a)) := ⟨(Monotone.monotoneOn · _), fun hf ↦ monotone_iff_forall_lt.2 <|
    AddConstMapClass.rel_map_of_Icc ha fun _x hx _y hy hxy ↦ hf hx hy hxy.le⟩

