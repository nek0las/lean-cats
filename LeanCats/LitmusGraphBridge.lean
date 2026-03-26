/-
  LitmusGraphBridge.lean

  Conversion from `LitmusParser.ConcreteCandExec` to `LitmusGraph.ConcreteExecution`.

  The two types represent the same concept — a concrete candidate execution — but
  with different representations:
-/
import LeanCats.LitmusGraph
import LeanCats.LitmusParser

open Data Litmus LitmusParser LitmusGraph

namespace LitmusGraphBridge

/-- Convert a `CEvent` (from LitmusParser) to a `Data.Event` (used by LitmusGraph).

  Field mapping:
  - `CEvent.id`     → `Event.id`
  - `CEvent.t_id`   → `Event.t_id`
  - `CEvent.op`     → `Event.effect.op`
  - `CEvent.loc`    → `Event.effect.location`
  - `CEvent.val`    → `Event.effect.value`
  - `CEvent.isInit` → `Event.effect.isFirstWrite`
  - `Event.tag`     is set to `⟨Normal, Normal.none⟩` (no extended tag information
                    is produced by the litmus parser)
-/
def ceventToEvent (e : CEvent) : Data.Event := {
  id     := e.id
  t_id   := e.t_id
  effect := {
    op           := e.op
    location     := e.loc
    value        := e.val
    isFirstWrite := e.isInit
    isFinalWrite := false     -- not tracked by the parser; inferred by model checkers
  }
  tag := ⟨Litmus.Normal, Litmus.Normal.none⟩
}

/-- Convert a `ConcreteCandExec` (LitmusParser) to a `ConcreteExecution` (LitmusGraph).

  Parameters:
  - `candExec` — the parsed candidate execution from LitmusParser

  The initial-write thread id is inferred automatically from `candExec.initWrites`.
  Program threads are labelled `P0`, `P1`, …; the init-write thread is labelled `IW`.

  Relations (`po`, `rf`, `co`, `fr`) in `ConcreteCandExec` are stored as
  `Array (Nat × Nat)` (pairs of event ids).  This function builds a hash map
  from id to `Data.Event` and uses it to lift each pair to `(Data.Event × Data.Event)`.
  Location names are recovered directly from `candExec.allEvents` via `CEvent.locName`.
-/
def candExecToConcreteExec
    (candExec : ConcreteCandExec)
    : LitmusGraph.ConcreteExecution :=
  -- 1. Convert every CEvent to a Data.Event
  let events := candExec.allEvents.map ceventToEvent

  -- 1.5. Build a location-id → location-name lookup table from the parser events
  let locMap : Std.HashMap Nat String :=
    candExec.allEvents.foldl (fun acc e =>
      if e.locName.isEmpty then acc else acc.insert e.loc e.locName) {}

  -- 2. Build an id → Event lookup table
  let idMap : Std.HashMap Nat Data.Event :=
    events.foldl (fun acc e => acc.insert e.id e) {}

  -- 3. Lift a relation from (Nat × Nat) to (Event × Event), dropping missing ids
  let convertRel (rel : Array (Nat × Nat)) : Array (Data.Event × Data.Event) :=
    rel.filterMap fun (srcId, tgtId) => do
      let src ← idMap.get? srcId
      let tgt ← idMap.get? tgtId
      return (src, tgt)

  -- 4. Determine the init-write thread id (used for labelling)
  let initTid : Nat :=
    match candExec.initWrites[0]? with
    | some (e : CEvent) => e.t_id
    | none   => Nat.succ (events.foldl (fun m (e : Data.Event) => max m e.t_id) 0)

  {
    events     := events
    locName    := fun n => (locMap.get? n).getD s!"loc{n}"
    threadName := fun n => if n == initTid then "IW" else s!"P{n}"
    po         := convertRel candExec.po
    rf         := convertRel candExec.rf
    co         := convertRel candExec.co
    fr         := convertRel candExec.fr
    rmw        := #[]
  }

end LitmusGraphBridge
