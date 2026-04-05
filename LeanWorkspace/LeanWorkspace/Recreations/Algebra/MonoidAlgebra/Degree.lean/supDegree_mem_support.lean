import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

variable [AddZeroClass A]

theorem supDegree_mem_support (hD : D.Injective) (hp : p ≠ 0) :
    D.invFun (p.supDegree D) ∈ p.support := by
  obtain ⟨a, ha, he⟩ := AddMonoidAlgebra.exists_supDegree_mem_support D hp
  rwa [he, Function.leftInverse_invFun hD]

