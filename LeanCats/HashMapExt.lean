import Std.Data.HashMap
import Lean

open Lean
open Std

-- HashMap Extention:
-- Copied from https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/HashMap.20extension
def HashMapExtension (α β : Type) [BEq α] [Hashable α] := SimplePersistentEnvExtension (α × β) (HashMap α β)

instance (α β : Type) [BEq α] [Hashable α] : Inhabited (HashMapExtension α β) :=
  inferInstanceAs (Inhabited (SimplePersistentEnvExtension (α × β) (HashMap α β)))

def mkHashMapExtension (name : Name) (α β : Type) [BEq α] [Hashable α]  : IO (HashMapExtension α β) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := mkStateFromImportedEntries (λ s n => s.insert n.1 n.2) {},
    addEntryFn    := (λ s n => s.insert n.1 n.2),
    toArrayFn     := fun es => es.toArray
  }

namespace HashMapExtension

variable {α β : Type} [BEq α] [Hashable α] {m: Type → Type} [Monad m] [MonadEnv m]

def find? (ext : HashMapExtension α β) (a : α) : m $ Option β := do
  return (ext.getState (← getEnv)).get? a

def insert (ext : HashMapExtension α β) (a : α) (b : β) : m Unit :=
  modifyEnv (ext.addEntry · (a, b))

def update (ext : HashMapExtension α β) (a : α) (b : β) : m Unit :=
  modifyEnv (ext.addEntry · (a, b))

end HashMapExtension
