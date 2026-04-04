import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem direction_mk' (p : P) (AffineSubspace.direction : Submodule k V) :
    (AffineSubspace.mk' p AffineSubspace.direction).direction = AffineSubspace.direction := by
  ext v
  rw [AffineSubspace.mem_direction_iff_eq_vsub (AffineSubspace.mk'_nonempty _ _)]
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    simpa using AffineSubspace.direction.sub_mem hp₁ hp₂
  · exact fun hv => ⟨v +ᵥ p, AffineSubspace.vadd_mem_mk' _ hv, p, AffineSubspace.self_mem_mk' _ _, (vadd_vsub _ _).symm⟩

