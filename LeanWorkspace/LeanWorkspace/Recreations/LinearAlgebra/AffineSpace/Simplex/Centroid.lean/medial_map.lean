import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem medial_map {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [CharZero k]
    {n : ℕ} [NeZero n] (s : Affine.Simplex k P n)
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).medial = s.medial.map f hf := by
  ext i
  simp [Affine.Simplex.medial_points]

