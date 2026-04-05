import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

theorem prod_map_le_pow_length₀ {F L : Type*} [FunLike F L R] {f : F} {r : R} {t : List L}
    (hf0 : ∀ x ∈ t, 0 ≤ f x) (hf : ∀ x ∈ t, f x ≤ r) :
    (map f t).prod ≤ r ^ length t := by
  convert List.prod_map_le_prod_map₀ f (Function.const L r) hf0 hf
  simp [map_const, prod_replicate]

omit [PosMulMono R]

