FAIL
import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c ∈ NonUnitalAlgebra.adjoin R {b}) (h : Commute a b) :
    Commute a c := by
  let S : NonUnitalSubalgebra R A :=
    { carrier := {x : A | Commute a x}
      zero_mem' := by
        simpa using Commute.zero_right a
      add_mem' := by
        intro x y hx hy
        exact hx.add_right hy
      mul_mem' := by
        intro x y hx hy
        exact hx.mul_right hy
      smul_mem' := by
        intro r x hx
        simpa [Algebra.smul_def] using hx.mul_left (algebraMap R A r) }
  have hb : b ∈ S := by
    simpa [S] using h
  have hle : NonUnitalAlgebra.adjoin R {b} ≤ S :=
    NonUnitalAlgebra.adjoin_le fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      simpa [hx] using hb
  exact hle hc
