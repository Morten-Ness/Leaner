import Mathlib

variable {F M N R α : Type*}

variable [NonUnitalNonAssocSemiring α]

variable [Monoid M] [Monoid N] [Semiring R]

variable [DistribMulAction M α] [SMulCommClass M α α] [IsScalarTower M α α]

variable [DistribMulAction N α] [SMulCommClass N α α] [IsScalarTower N α α]

variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

variable {R : Type*}

variable [CommSemiring R]

theorem _root_.NonUnitalNonAssocSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ R a = L a ∧ (L a) ∈ RingHom.rangeS (CentroidHom.toEndRingHom α) := by
  constructor
  · exact fun ha ↦ ⟨AddMonoidHom.ext <| fun _ => (IsMulCentral.comm ha _).symm,
      ⟨CentroidHom.centerToCentroid ⟨a, ha⟩, rfl⟩⟩
  · rintro ⟨hc, ⟨T, hT⟩⟩
    have e1 (d : α) : T d = a * d := congr($hT d)
    have e2 (d : α) : T d = d * a := congr($(hT.trans hc.symm) d)
    constructor
    case comm => exact (congr($hc.symm ·))
    case left_assoc => simpa [e1] using (map_mul_right T · ·)
    case right_assoc => simpa [e2] using (map_mul_left T · ·)

