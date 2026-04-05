import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem _root_.Set.smul_mem_centralizer {s : Set A} (r : R) {a : A} (ha : a ∈ s.centralizer) :
    r • a ∈ s.centralizer := fun x hx => by rw [mul_smul_comm, smul_mul_assoc, ha x hx]

