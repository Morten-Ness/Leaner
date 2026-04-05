import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem antitone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Antitone f ↔ AntitoneOn f (Icc l (l + a)) := AddConstMapClass.monotone_iff_Icc (H := Hᵒᵈ) ha l

