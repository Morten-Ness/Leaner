import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ NonUnitalAlgebra.adjoin R s) (h : ∀ b ∈ s, Commute a b) :
    Commute a b := by
  let S : NonUnitalSubalgebra R A :=
    { carrier := {x : A | Commute a x}
      mul_mem' := by
        intro x y hx hy
        exact hx.mul_right hy
      add_mem' := by
        intro x y hx hy
        exact hx.add_right hy
      zero_mem' := by
        simpa using (Commute.zero_right a)
      smul_mem' := by
        intro r x hx
        exact hx.smul_right r }
  have hs : s ⊆ S := by
    intro x hx
    exact h x hx
  have hadj : NonUnitalAlgebra.adjoin R s ≤ S :=
    NonUnitalAlgebra.adjoin_le hs
  exact hadj hb
