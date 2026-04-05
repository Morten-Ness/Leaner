import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Semiring R] [StarRing R]
  [NonUnitalSemiring A] [StarRing A] [Module R A]
  [StarModule R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem smul_mem_closure_star_mul {r : R}
    (hr : r ∈ AddSubmonoid.closure (Set.range fun s ↦ star s * s)) {a : A}
    (ha : a ∈ AddSubmonoid.closure (Set.range fun s ↦ star s * s)) :
    r • a ∈ AddSubmonoid.closure (Set.range fun s ↦ star s * s) := by
  induction hr using AddSubmonoid.closure_induction with
  | zero => simp
  | add r₁ r₂ _ _ hr₁ hr₂ => simpa [add_smul] using add_mem hr₁ hr₂
  | mem r hr =>
  induction ha using AddSubmonoid.closure_induction with
  | zero => simp
  | add a₁ a₂ _ _ ha₁ ha₂ => simpa [smul_add] using add_mem ha₁ ha₂
  | mem a ha =>
  obtain ⟨r, rfl⟩ := hr
  obtain ⟨a, rfl⟩ := ha
  exact AddSubmonoid.subset_closure ⟨r • a, by simp [star_smul, smul_mul_smul_comm]⟩

