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
-- § Ordered (Column) Layout Renderer
-- ════════════════════════════════════════════════════════════════

/-! The ordered renderer places events in a grid:

* **Columns** = one per thread, with the IW (initial-write) thread first.
* **Rows**    = events within a thread, top-to-bottom in program order (by event id).

Relation edges are drawn as SVG paths between the fixed node positions.
`po` edges are straight vertical arrows within a column;
cross-column edges (`rf`, `co`, `fr`, `rmw`) use quadratic Bézier curves.
-/

/-- Layout configuration for the ordered graph. -/
structure LayoutCfg where
  colSpacing : Float := 180
  rowSpacing : Float := 70
  marginX    : Float := 80
  marginY    : Float := 60
  nodeW      : Float := 110
  nodeH      : Float := 28
deriving Inhabited

/-- Helper: build a string-valued SVG attribute pair. -/
private def sa (k v : String) : String × Lean.Json := (k, Lean.Json.str v)
/-- Helper: build a numeric SVG attribute pair (float → string). -/
private def sn (k : String) (v : Float) : String × Lean.Json := (k, Lean.Json.str (toString v))

/-- Build the ordered-layout SVG for a `ConcreteExecution`.
Returns a self-contained `<svg>` `Html` element. -/
def executionToOrderedSvg (exec : ConcreteExecution) (cfg : LayoutCfg := {}) : Html := Id.run do
  -- ── 1. Group threads, IW first ─────────────────────────────
  let initTid := exec.events.foldl
    (fun acc e => if e.effect.isFirstWrite then e.t_id else acc) 0
  let allTids := ((exec.events.map (·.t_id)).toList).eraseDups
  let sortedTids :=
    allTids.filter (· == initTid) ++
    (allTids.filter (· != initTid)).mergeSort (· < ·)

  -- ── 2. Position map: event id → (cx, cy) ──────────────────
  let mut posMap : Std.HashMap Nat (Float × Float) := {}
  let mut colIdx : Nat := 0
  let mut maxRows : Nat := 0
  for tid in sortedTids do
    let threadEvts := exec.events.filter (·.t_id == tid)
    let sorted := threadEvts.qsort (fun a b => a.id < b.id)
    let cx := cfg.marginX + cfg.colSpacing * colIdx.toFloat
    for rowIdx in [:sorted.size] do
      let cy := cfg.marginY + cfg.rowSpacing * rowIdx.toFloat
      posMap := posMap.insert sorted[rowIdx]!.id (cx, cy)
    maxRows := max maxRows sorted.size
    colIdx := colIdx + 1
  let numCols := colIdx

  -- ── 3. Canvas size ─────────────────────────────────────────
  let svgW := cfg.marginX * 2 + cfg.colSpacing * (numCols.toFloat - 1) + cfg.nodeW
  let svgH := cfg.marginY + cfg.rowSpacing * (maxRows.toFloat - 1) + cfg.nodeH + 40

  -- ── 4. Defs: colored arrowhead markers ─────────────────────
  let mkArrow (id color : String) := Html.element "marker"
    #[sa "id" id,
      sa "markerWidth" "10", sa "markerHeight" "7",
      sa "refX" "10", sa "refY" "3.5",
      sa "orient" "auto"]
    #[Html.element "polygon"
        #[sa "points" "0 0, 10 3.5, 0 7", sa "fill" color] #[]]
  let defs := Html.element "defs" #[]
    #[mkArrow "arrow-po"  "cornflowerblue",
      mkArrow "arrow-rf"  "seagreen",
      mkArrow "arrow-co"  "tomato",
      mkArrow "arrow-fr"  "orange",
      mkArrow "arrow-rmw" "purple"]

  -- ── 5. Column headers ──────────────────────────────────────
  let mut headers : Array Html := #[]
  let mut ci : Nat := 0
  for tid in sortedTids do
    let cx := cfg.marginX + cfg.colSpacing * ci.toFloat
    headers := headers.push (Html.element "text"
      #[sn "x" cx, sn "y" 20,
        sa "textAnchor" "middle", sa "dominantBaseline" "middle",
        sa "fill" "var(--vscode-editor-foreground)",
        sa "fontSize" "14", sa "fontWeight" "bold"]
      #[Html.text (exec.threadName tid)])
    ci := ci + 1

  -- ── 6. Event nodes ─────────────────────────────────────────
  let mut nodes : Array Html := #[]
  for e in exec.events do
    let some (cx, cy) := posMap[e.id]? | continue
    let color := threadColor e.t_id initTid
    let label := s!"{exec.threadName e.t_id}: {eventDisplayName e exec.locName}"
    let halfW := cfg.nodeW / 2
    let halfH := cfg.nodeH / 2
    let rect := Html.element "rect"
      #[sn "x" (cx - halfW), sn "y" (cy - halfH),
        sn "width" cfg.nodeW, sn "height" cfg.nodeH,
        sa "rx" "4", sa "ry" "4",
        sa "fill" "var(--vscode-editor-background)",
        sa "stroke" color, sa "strokeWidth" "1.5"] #[]
    let txt := Html.element "text"
      #[sn "x" cx, sn "y" cy,
        sa "textAnchor" "middle", sa "dominantBaseline" "middle",
        sa "fill" color, sa "fontSize" "11"]
      #[Html.text label]
    nodes := nodes.push (Html.element "g" #[] #[rect, txt])

  -- ── 7. Edges ───────────────────────────────────────────────
  let shorten (x1 y1 x2 y2 gap : Float) :=
    let dx := x2 - x1; let dy := y2 - y1
    let len := Float.sqrt (dx * dx + dy * dy)
    if len < 0.01 then (x1, y1, x2, y2)
    else let u := dx / len; let v := dy / len
         (x1 + u * gap, y1 + v * gap, x2 - u * gap, y2 - v * gap)

  let mut edges : Array Html := #[]
  let allRels : Array (RelationStyle × Array (Event × Event)) := #[
    (poStyle, exec.po), (rfStyle, exec.rf), (coStyle, exec.co),
    (frStyle, exec.fr), (rmwStyle, exec.rmw)]

  for (style, pairs) in allRels do
    let arrowUrl := s!"url(#arrow-{style.name})"
    for (src, tgt) in pairs do
      let some (sx, sy) := posMap[src.id]? | continue
      let some (tx, ty) := posMap[tgt.id]? | continue
      let (sx', sy', tx', ty') := shorten sx sy tx ty (cfg.nodeH / 2 + 4)
      let sameCol := (sx - tx).abs < 1.0
      let pathD :=
        if sameCol then s!"M {sx'} {sy'} L {tx'} {ty'}"
        else
          let dx := tx' - sx'; let dy := ty' - sy'
          let len := Float.sqrt (dx * dx + dy * dy)
          let off := if 30 < len * 0.15 then 30 else len * 0.15
          let px := -dy / len * off; let py := dx / len * off
          let cpx := (sx' + tx') / 2 + px; let cpy := (sy' + ty') / 2 + py
          s!"M {sx'} {sy'} Q {cpx} {cpy} {tx'} {ty'}"
      let dashAt : Array (String × Lean.Json) :=
        if style.dashed then #[sa "strokeDasharray" "6,3"] else #[]
      let path := Html.element "path"
        (#[sa "d" pathD, sa "stroke" style.color,
           sa "strokeWidth" "2", sa "fill" "none",
           sa "markerEnd" arrowUrl] ++ dashAt) #[]
      -- Label at midpoint (offset for curves)
      let (lx, ly) :=
        if sameCol then ((sx' + tx') / 2 + 18, (sy' + ty') / 2)
        else
          let dx := tx' - sx'; let dy := ty' - sy'
          let len := Float.sqrt (dx * dx + dy * dy)
          let off := if 30 < len * 0.15 then 30 else len * 0.15
          let px := -dy / len * off; let py := dx / len * off
          ((sx' + tx') / 2 + px * 0.6, (sy' + ty') / 2 + py * 0.6 - 8)
      let lbl := Html.element "text"
        #[sn "x" lx, sn "y" ly,
          sa "textAnchor" "middle", sa "dominantBaseline" "middle",
          sa "fill" style.color, sa "fontSize" "10", sa "fontWeight" "bold"]
        #[Html.text style.name]
      edges := edges.push (Html.element "g" #[] #[path, lbl])

  -- ── 8. Assemble SVG ────────────────────────────────────────
  let bg := Html.element "rect"
    #[sa "width" "100%", sa "height" "100%",
      sa "fill" "var(--vscode-editor-background)"] #[]
  Html.element "svg"
    #[sn "width" svgW, sn "height" svgH,
      sa "xmlns" "http://www.w3.org/2000/svg",
      ("style", Lean.Json.mkObj [
        ("border", "1px solid var(--vscode-panel-border)"),
        ("borderRadius", "4px")])]
    (#[defs, bg] ++ headers ++ nodes ++ edges)

/-- Render a `ConcreteExecution` as an ordered (column-layout) HTML widget. -/
def toOrderedHtml (exec : ConcreteExecution) (cfg : LayoutCfg := {}) : Html :=
  executionToOrderedSvg exec cfg

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
#html toOrderedHtml sbExecution

end LitmusGraph
