import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : StarSubsemiring R → Subsemiring R) := fun S T h =>
  StarSubsemiring.ext fun x => by rw [← StarSubsemiring.mem_toSubsemiring, ← StarSubsemiring.mem_toSubsemiring, h]

