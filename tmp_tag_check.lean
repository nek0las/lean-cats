import LeanCats.Data
import LeanCats.Macro
open Data

def e : Data.Event :=
  { id := 1, t_id := 0,
    effect := { op := Data.Op.read, location := 0, value := some 0, isFirstWrite := false, isFinalWrite := false },
    tag := ⟨lkmm.Accesses, lkmm.Accesses.ONCE'⟩ }
