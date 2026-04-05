import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulMono α R] {x : Matrix n n R}
    (hx : x.PosSemidef) {a : α} (ha : 0 ≤ a) : (a • x).PosSemidef := by
  refine ⟨IsSelfAdjoint.smul (.of_nonneg ha) hx.1, fun y => ?_⟩
  simpa [mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using smul_nonneg ha (hx.2 _)

protected lemma zero : Matrix.PosSemidef (0 : Matrix n n R) := ⟨isHermitian_zero, by simp⟩

protected lemma one [StarOrderedRing R] [DecidableEq n] : Matrix.PosSemidef (1 : Matrix n n R) :=
  ⟨isHermitian_one, fun x => Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [*]⟩

