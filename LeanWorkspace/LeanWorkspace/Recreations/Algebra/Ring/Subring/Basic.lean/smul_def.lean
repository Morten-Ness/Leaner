import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {α β : Type*}

theorem smul_def [SMul R α] {S : Subring R} (g : S) (m : α) : g • m = (g : R) • m := rfl

example [SMul R β] [SMul α β] [SMulCommClass R α β] (S : Subring R) :
    SMulCommClass S α β := by infer_instance

example [SMul α β] [SMul R β] [SMulCommClass α R β] (S : Subring R) :
    SMulCommClass α S β := by infer_instance

