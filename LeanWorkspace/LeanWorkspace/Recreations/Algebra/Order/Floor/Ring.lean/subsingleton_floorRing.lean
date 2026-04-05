import Mathlib

variable {F R S : Type*}

theorem subsingleton_floorRing {R} [Ring R] [LinearOrder R] : Subsingleton (FloorRing R) := by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.floor = H₂.floor :=
    funext fun a => (H₁.gc_coe_floor.u_unique H₂.gc_coe_floor) fun _ => rfl
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil_coe.l_unique H₂.gc_ceil_coe) fun _ => rfl
  cases H₁; cases H₂; congr

