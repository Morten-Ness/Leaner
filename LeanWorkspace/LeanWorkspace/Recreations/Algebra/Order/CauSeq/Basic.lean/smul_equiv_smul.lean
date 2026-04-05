import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem smul_equiv_smul {G : Type*} [SMul G β] [IsScalarTower G β β] {f1 f2 : CauSeq β abv} (c : G)
    (hf : f1 ≈ f2) : c • f1 ≈ c • f2 := by
  simpa [CauSeq.const_smul, smul_one_mul _ _] using
    CauSeq.mul_equiv_mul (CauSeq.const_equiv.mpr <| Eq.refl <| c • (1 : β)) hf

