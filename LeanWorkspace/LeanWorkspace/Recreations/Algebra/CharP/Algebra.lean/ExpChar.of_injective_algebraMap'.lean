import Mathlib

variable {R A : Type*}

theorem ExpChar.of_injective_algebraMap' [CommRing R] [CommRing A]
    [Algebra R A] [FaithfulSMul R A] (q : ℕ) [ExpChar R q] : ExpChar A q := expChar_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) q

