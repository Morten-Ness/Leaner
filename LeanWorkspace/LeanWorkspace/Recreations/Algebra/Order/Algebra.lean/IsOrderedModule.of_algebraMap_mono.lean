import Mathlib

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

theorem IsOrderedModule.of_algebraMap_mono [PosMulMono β] [MulPosMono β]
    (h : Monotone (algebraMap α β)) : IsOrderedModule α β := .of_smul_one_mono (by simpa [Algebra.smul_def] using h)

