import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem median_map [CharZero k] {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1))
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).median i = (s.median i).map f := by
  simp [Affine.Simplex.median, map_span, Set.image_pair]

