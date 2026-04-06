FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

theorem comap_map_eq_self {f : A →ₐ[R] B} {S : Subalgebra R A}
    (h : f ⁻¹' {0} ⊆ S) : (S.map f).comap f = S := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hyS, hyEq⟩
    have hxy : x - y ∈ S := by
      apply h
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [map_sub, hyEq, sub_self]
    have hx' : x = (x - y) + y := (sub_add_cancel x y).symm
    rw [hx']
    exact S.add_mem hxy hyS
  · intro hx
    exact ⟨x, hx, rfl⟩
