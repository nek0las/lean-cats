import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.HtmlDisplay
import LeanCats.Litmus

/-! ## Execution Graph Visualization

This file provides a general-purpose function `executionToGraph` that converts a
concrete candidate execution into an interactive directed graph using
ProofWidgets4 `GraphDisplay`.

Each event in the execution becomes a single vertex (keyed by its event id).
Relations (`po`, `rf`, `co`, `fr`, `rmw`) are iterated and each pair becomes a
directed edge. Events appearing in multiple relations share the **same** vertex —
no duplicates are created.

**Edge color legend:**
- **Blue (cornflowerblue)** — `po` (program order, within a thread)
- **Green (seagreen)** — `rf` (read-from, write → read)
- **Red (tomato)** — `co` (coherence order, write → write)
- **Orange (dashed)** — `fr` (from-read = rf⁻¹;co)
- **Purple** — `rmw` (read-modify-write)

Place cursor on the `#html` command in VS Code to see the interactive graph.
-/

open ProofWidgets Jsx Data Litmus

-- Event contains a Sigma-typed tag field, so we provide a default instance manually.
instance : Inhabited Event where
  default := {
    id := 0, t_id := 0,
    effect := { op := .write, location := 0, value := none, isFirstWrite := false, isFinalWrite := false },
    tag := ⟨Litmus.Normal, Litmus.Normal.none⟩
  }

namespace LitmusGraph

-- ════════════════════════════════════════════════════════════════
-- § SVG Helpers
-- ════════════════════════════════════════════════════════════════

/-- Create an SVG label for a vertex: a rounded rectangle with text. -/
def mkLabel (text : String) (color : String := "var(--vscode-editor-foreground)") : Html :=
  <g>
    <rect x={.num (-45)} y={.num (-12)} width={90} height={24} rx={4} ry={4}
      fill="var(--vscode-editor-background)"
      stroke={color}
      strokeWidth={.num 1.5} />
    <text textAnchor="middle" dominantBaseline="middle"
      fill={color}
      fontSize="11">{.text text}</text>
  </g>

/-- Create an SVG label for an edge. -/
def mkEdgeLabel (text : String) (color : String) : Html :=
  <g>
    <text textAnchor="middle" dominantBaseline="middle"
      fill={color}
      fontSize="10"
      fontWeight="bold">{.text text}</text>
  </g>

-- ════════════════════════════════════════════════════════════════
-- § Relation Styling
-- ════════════════════════════════════════════════════════════════

/-- Visual style for a relation in the execution graph. -/
structure RelationStyle where
  name  : String
  color : String
  dashed : Bool := false
deriving Inhabited

def poStyle  : RelationStyle := { name := "po",  color := "cornflowerblue" }
def rfStyle  : RelationStyle := { name := "rf",  color := "seagreen" }
def coStyle  : RelationStyle := { name := "co",  color := "tomato" }
def frStyle  : RelationStyle := { name := "fr",  color := "orange", dashed := true }
def rmwStyle : RelationStyle := { name := "rmw", color := "purple" }

-- ════════════════════════════════════════════════════════════════
-- § Display Helpers
-- ════════════════════════════════════════════════════════════════

/-- Default thread color palette. -/
def defaultThreadColors : Array String :=
  #["#4488ff", "#ff8844", "#44bb44", "#bb44bb", "#44bbbb", "#ffcc00"]

/-- Get a color for a thread, with a special gray for the initial-write thread. -/
def threadColor (t_id : Nat) (initThreadId : Nat) : String :=
  if t_id == initThreadId then "#888"
  else defaultThreadColors[t_id % defaultThreadColors.size]!

/-- Short display string for an operation kind. -/
def opString : Op → String
  | .write  => "W"
  | .read   => "R"
  | .fence  => "F"
  | .branch => "B"

/-- Human-readable display name for an event, e.g. `"W x=1"` or `"R y"`. -/
def eventDisplayName (e : Event) (locName : Nat → String) : String :=
  let op  := opString e.effect.op
  let loc := locName e.effect.location
  match e.effect.value with
  | some v => s!"{op} {loc}={v}"
  | none   => s!"{op} {loc}"

-- ════════════════════════════════════════════════════════════════
-- § Concrete Execution
-- ════════════════════════════════════════════════════════════════

/-- A concrete (computationally enumerable) candidate execution for visualization.

Unlike `CandidateExecution` (which uses `Set`-based relations that cannot be iterated),
this structure stores every relation as an `Array` of event pairs so that
`executionToGraph` can traverse them to build vertices and edges. -/
structure ConcreteExecution where
  /-- All events participating in the execution. -/
  events     : Array Event
  /-- Map a memory-location id to a readable name (e.g. `0 ↦ "x"`). -/
  locName    : Nat → String
  /-- Map a thread id to a readable name (e.g. `0 ↦ "P0"`). -/
  threadName : Nat → String
  /-- Program-order edges (typically *direct* — consecutive within a thread). -/
  po  : Array (Event × Event)
  /-- Read-from edges. -/
  rf  : Array (Event × Event)
  /-- Coherence-order edges. -/
  co  : Array (Event × Event)
  /-- From-read edges (`rf⁻¹ ; co`). -/
  fr  : Array (Event × Event)
  /-- Read-modify-write edges. -/
  rmw : Array (Event × Event) := #[]

-- ════════════════════════════════════════════════════════════════
-- § Computation Helpers
-- ════════════════════════════════════════════════════════════════

/-- Compute *direct* (immediate-successor) program-order edges from an event list.
Events are grouped by thread, sorted by id, and consecutive pairs are connected. -/
def computeDirectPo (events : Array Event) : Array (Event × Event) := Id.run do
  let mut result : Array (Event × Event) := #[]
  -- collect unique thread ids
  let threadIds := ((events.map (·.t_id)).toList).eraseDups
  for tid in threadIds do
    let threadEvts := events.filter (·.t_id == tid)
    let sorted := threadEvts.qsort (fun a b => a.id < b.id)
    for i in [:sorted.size - 1] do
      result := result.push (sorted[i]!, sorted[i + 1]!)
  return result

/-- Compute from-read edges: `fr = rf⁻¹ ; co`.
For every `(w, r) ∈ rf` and `(w', w'') ∈ co` with `w = w'`, emit `(r, w'')`. -/
def computeFr (rf co : Array (Event × Event)) : Array (Event × Event) := Id.run do
  let mut result : Array (Event × Event) := #[]
  for (w, r) in rf do
    for (w', w'') in co do
      if w.id == w'.id then
        result := result.push (r, w'')
  return result

-- ════════════════════════════════════════════════════════════════
-- § Graph Conversion
-- ════════════════════════════════════════════════════════════════

/-- Build the SVG edge attributes for a given relation style. -/
private def edgeAttrs (style : RelationStyle) : Array (String × Lean.Json) :=
  let base : Array (String × Lean.Json) :=
    #[("stroke", Lean.Json.str style.color),
      ("strokeWidth", (2 : Lean.Json)),
      ("markerEnd", Lean.Json.str "url(#arrow)")]
  if style.dashed
  then base.push ("strokeDasharray", Lean.Json.str "5,3")
  else base

/-- Convert a `ConcreteExecution` into ProofWidgets `GraphDisplay` vertices and edges.

* Each event becomes **one** vertex, identified by `toString event.id`.
* Every pair `(a, b)` in every relation becomes a directed edge `a → b`
  with the relation's color/label.
* Events that appear in multiple relations share the same vertex — they are
  connected directly rather than duplicated. -/
def executionToGraph (exec : ConcreteExecution)
    : Array GraphDisplay.Vertex × Array GraphDisplay.Edge := Id.run do
  -- Detect the initial-write thread id
  let initThreadId := exec.events.foldl
    (fun acc e => if e.effect.isFirstWrite then e.t_id else acc) 10

  -- ── vertices ──────────────────────────────────────────────
  let mut vertices : Array GraphDisplay.Vertex := #[]
  for e in exec.events do
    let tLabel := exec.threadName e.t_id
    let eName  := eventDisplayName e exec.locName
    let color  := threadColor e.t_id initThreadId
    vertices := vertices.push {
      id            := toString e.id
      label         := mkLabel s!"{tLabel}: {eName}" color
      boundingShape := .rect 90 24
      details?      := some <span>{.text s!"Event {e.id} (thread {tLabel}): {eName}"}</span>
    }

  -- ── edges ─────────────────────────────────────────────────
  let mut edges : Array GraphDisplay.Edge := #[]
  let allRelations : Array (RelationStyle × Array (Event × Event)) := #[
    (poStyle,  exec.po),
    (rfStyle,  exec.rf),
    (coStyle,  exec.co),
    (frStyle,  exec.fr),
    (rmwStyle, exec.rmw)
  ]

  for (style, pairs) in allRelations do
    for (src, tgt) in pairs do
      edges := edges.push {
        source   := toString src.id
        target   := toString tgt.id
        attrs    := edgeAttrs style
        label?   := some (mkEdgeLabel style.name style.color)
        details? := some <span>{.text s!"{style.name}: event {src.id} → event {tgt.id}"}</span>
      }

  return (vertices, edges)

/-- Build graph data and render it. -/
private def toHtmlAux (verts : Array GraphDisplay.Vertex) (edgs : Array GraphDisplay.Edge) : Html :=
  <GraphDisplay
    vertices={verts}
    edges={edgs}
    forces={#[
      .link { distance? := some 150 },
      .manyBody { strength? := some (-300) },
      .x {},
      .y {}
    ]}
    showDetails={true}
  />

/-- Render a `ConcreteExecution` as an interactive HTML graph widget. -/
def toHtml (exec : ConcreteExecution) : Html :=
  let data := executionToGraph exec
  toHtmlAux data.1 data.2

-- ════════════════════════════════════════════════════════════════
-- § Example — X86 SB (Store Buffering) Litmus Test
-- ════════════════════════════════════════════════════════════════

/-! ### X86 SB (Store Buffering) Litmus Test

```
{ x=0; y=0; }
 P0              | P1
 (1) MOV [x],$1  | (3) MOV [y],$1
 (2) MOV EAX,[y] | (4) MOV EAX,[x]

exists (0:EAX=0 ∧ 1:EAX=0)
```
-/

private def sbEvents : Array Event :=
  #[initWx, initWy, inst1writeX, inst2readY, inst3writeY, inst4readX]

private def sbRf : Array (Event × Event) :=
  #[(initWy, inst2readY), (inst1writeX, inst4readX)]

private def sbCo : Array (Event × Event) :=
  #[(initWx, inst1writeX), (initWy, inst3writeY)]

/-- Concrete SB litmus-test execution, built from the events and relations
defined in `Litmus.lean`. -/
def sbExecution : ConcreteExecution := {
  events     := sbEvents
  locName    := fun n => match n with | 0 => "x" | 1 => "y" | _ => s!"loc{n}"
  threadName := fun n => match n with | 0 => "P0" | 1 => "P1" | 10 => "IW" | _ => s!"T{n}"
  po         := computeDirectPo sbEvents
  rf         := sbRf
  co         := sbCo
  fr         := computeFr sbRf sbCo
  rmw        := #[]
}

-- Place your cursor on the line below in VS Code to see the execution graph.
#html toHtml sbExecution

end LitmusGraph
