import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

variable [Add B]

variable [AddLeftStrictMono B] [AddRightStrictMono B]

set_option backward.isDefEq.respectTransparency false in
theorem apply_supDegree_add_supDegree (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q) (D.invFun (p.supDegree D + q.supDegree D)) = p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | hq := eq_or_ne q 0
  · simp
  obtain ⟨ap, -, hp⟩ := AddMonoidAlgebra.exists_supDegree_mem_support D hp
  obtain ⟨aq, -, hq⟩ := AddMonoidAlgebra.exists_supDegree_mem_support D hq
  simp_rw [AddMonoidAlgebra.leadingCoeff, hp, hq, ← hadd, Function.leftInverse_invFun hD _]
  exact AddMonoidAlgebra.apply_add_of_supDegree_le hadd hD hp.le hq.le

