import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem iterate_map_inv {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) :
    f^[n] x⁻¹ = (f^[n] x)⁻¹ := Commute.iterate_left (map_inv f) n x

