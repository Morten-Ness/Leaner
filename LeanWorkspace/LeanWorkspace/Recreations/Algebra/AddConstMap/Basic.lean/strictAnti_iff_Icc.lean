import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem strictAnti_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictAnti f ↔ StrictAntiOn f (Icc l (l + a)) := AddConstMapClass.strictMono_iff_Icc (H := Hᵒᵈ) ha l

