import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

variable (k P1)

variable {k P1}

variable {P1}

variable {k}

variable (k) in

theorem decomp (f : V1 →ᵃ[k] V2) : (f : V1 → V2) = ⇑f.linear + fun _ => f 0 := by
  ext x
  calc
    f x = f.linear x +ᵥ f 0 := by rw [← AffineMap.map_vadd f, vadd_eq_add, add_zero]
    _ = (f.linear + fun _ : V1 => f 0) x := rfl

