import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [One M] [One N]

variable [FunLike F M N]

theorem map_ne_one_iff {R S F : Type*} [One R] [One S] [FunLike F R S] [OneHomClass F R S] (f : F)
    (hf : Function.Injective f) {x : R} : f x ≠ 1 ↔ x ≠ 1 := (map_eq_one_iff f hf).not

