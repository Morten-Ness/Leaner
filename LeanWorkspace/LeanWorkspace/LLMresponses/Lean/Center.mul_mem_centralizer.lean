import Mathlib

variable {M : Type*} {S T : Set M}

variable [Semigroup M] {a b : M}

theorem mul_mem_centralizer (ha : a ∈ Set.centralizer S) (hb : b ∈ Set.centralizer S) :
    a * b ∈ Set.centralizer S := by
  intro s hs
  rw [Set.mem_centralizer_iff] at ha hb
  calc
    s * (a * b) = (s * a) * b := by rw [mul_assoc]
    _ = (a * s) * b := by rw [ha s hs]
    _ = a * (s * b) := by rw [← mul_assoc]
    _ = a * (b * s) := by rw [hb s hs]
    _ = (a * b) * s := by rw [mul_assoc]
