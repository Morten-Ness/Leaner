FAIL
import Mathlib

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem saturation_induction {s : Submonoid M}
    {p : (x : M) → x ∈ s.saturation → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (Submonoid.le_toSubmonoid_saturation hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (of_mul : ∀ (x y) (hxy : x * y ∈ s.saturation),
      p (x * y) hxy → p x (s.saturation.2 hxy).1 ∧ p y (s.saturation.2 hxy).2)
    {x : M} (hx : x ∈ s.saturation) : p x hx := by
  let q : ∀ y : M, y ∈ s.saturation → Prop := fun y hy => ∀ hz : y ∈ s, p y (Submonoid.le_toSubmonoid_saturation hz)
  have hq_mem : ∀ (y) (hy : y ∈ s), q y (Submonoid.le_toSubmonoid_saturation hy) := by
    intro y hy hz
    exact mem y hz
  have hq_mul :
      ∀ x y hx hy, q x hx → q y hy → q (x * y) (mul_mem hx hy) := by
    intro x y hx hy hpx hpy hz
    exact mul x y _ _ (hpx ((s.saturation.2 (Submonoid.le_toSubmonoid_saturation hz)).1))
      (hpy ((s.saturation.2 (Submonoid.le_toSubmonoid_saturation hz)).2))
  have hq_of_mul :
      ∀ (x y) (hxy : x * y ∈ s.saturation),
        q (x * y) hxy →
          q x (s.saturation.2 hxy).1 ∧ q y (s.saturation.2 hxy).2 := by
    intro x y hxy hqxy
    constructor <;> intro hz
    · exact (of_mul x y (Submonoid.le_toSubmonoid_saturation hz) (hqxy hz)).1
    · exact (of_mul x y (Submonoid.le_toSubmonoid_saturation hz) (hqxy hz)).2
  have hmain : q x hx := by
    exact saturation_induction hq_mem hq_mul hq_of_mul hx
  exact hmain ((show x ∈ s from by
    have := hmain
    sorry))
