import Mathlib

variable {C : Type*} [Category* C]

variable [Abelian C] (K L : CochainComplex C ℤ)

theorem shortComplexTruncLE_shortExact (n : ℤ) :
    (K.shortComplexTruncLE n).ShortExact := by
  apply HomologicalComplex.shortComplexTruncLE_shortExact

