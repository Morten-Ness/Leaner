import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z := ⟨fun hz => ⟨(EuclideanDomain.dvd_lcm_left _ _).trans hz, (EuclideanDomain.dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ =>
    EuclideanDomain.lcm_dvd hxz hyz⟩

