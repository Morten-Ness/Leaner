FAIL
import Mathlib

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (B : Type*) [Semiring B] [Algebra R B]

theorem centralizer_coe_map_includeRight_eq_center_tensorProduct
    (S : Subalgebra R B) [Module.Free R A] :
    Set.centralizer
      (↑(S.map (Algebra.TensorProduct.includeRight (R := R) (A := A))) :
        Set (TensorProduct R A B)) =
      Set.center (TensorProduct R A B) := by
  ext x
  simp only [Set.mem_centralizer_iff, Set.mem_center_iff]
  constructor
  · intro hx y
    induction y using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul a b =>
        have hy :
            Algebra.TensorProduct.includeRight (R := R) (A := A) b ∈
              (↑(S.map (Algebra.TensorProduct.includeRight (R := R) (A := A))) :
                Set (TensorProduct R A B)) := by
          exact ⟨b, by simpa using ‹b ∈ S›, rfl⟩
        simpa [Algebra.TensorProduct.includeRight] using
          hx (Algebra.TensorProduct.includeRight (R := R) (A := A) b) hy
    | add y z hy hz =>
        simpa [mul_add, add_mul, hy, hz]
  · intro hx y hy
    exact hx y
