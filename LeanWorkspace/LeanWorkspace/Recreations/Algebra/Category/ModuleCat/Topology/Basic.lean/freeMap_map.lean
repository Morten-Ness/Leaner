import Mathlib

variable (R : Type u) [Ring R] [TopologicalSpace R]

theorem freeMap_map {X Y : TopCat} (f : X ⟶ Y) (v : X →₀ R) :
    (TopModuleCat.freeMap R f : (X →₀ R) → (Y →₀ R)) v = Finsupp.mapDomain f.hom v := rfl

