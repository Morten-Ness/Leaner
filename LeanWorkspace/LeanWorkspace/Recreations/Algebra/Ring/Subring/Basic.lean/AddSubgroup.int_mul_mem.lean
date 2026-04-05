import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem AddSubgroup.int_mul_mem {G : AddSubgroup R} (k : ℤ) {g : R} (h : g ∈ G) :
    (k : R) * g ∈ G := by
  convert AddSubgroup.zsmul_mem G h k using 1
  rw [zsmul_eq_mul]

