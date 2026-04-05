import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.id_comp [MulOne M] [MulOne N] (f : M →* N) :
    (MonoidHom.id N).comp f = f := MonoidHom.ext fun _ => rfl

