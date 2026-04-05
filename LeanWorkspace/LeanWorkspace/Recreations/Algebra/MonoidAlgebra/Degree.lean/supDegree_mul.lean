import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

theorem supDegree_mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hpq : AddMonoidAlgebra.leadingCoeff D p * AddMonoidAlgebra.leadingCoeff D q ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  apply AddMonoidAlgebra.supDegree_eq_of_max
  · rw [← AddSubsemigroup.coe_set_mk (Set.range D), ← AddHom.srange_mk _ hadd, SetLike.mem_coe]
    · exact add_mem (AddMonoidAlgebra.supDegree_mem_range D hp) (AddMonoidAlgebra.supDegree_mem_range D hq)
    · exact (AddHom.srange ⟨D, hadd⟩).add_mem
  · simp_rw [Finsupp.mem_support_iff, AddMonoidAlgebra.apply_supDegree_add_supDegree hD hadd]
    exact hpq
  · have := addLeftMono_of_addLeftStrictMono B
    have := addRightMono_of_addRightStrictMono B
    exact fun a ha => (Finset.le_sup ha).trans (AddMonoidAlgebra.supDegree_mul_le hadd)

