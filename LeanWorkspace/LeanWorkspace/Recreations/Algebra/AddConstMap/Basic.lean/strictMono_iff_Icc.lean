import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem strictMono_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictMono f ↔ StrictMonoOn f (Icc l (l + a)) := ⟨(StrictMono.strictMonoOn · _), AddConstMapClass.rel_map_of_Icc ha⟩

