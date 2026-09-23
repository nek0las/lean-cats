import LeanCats.CatParser.Macro
import LeanCats.Basic

namespace Std
open Data

@[simp] def domain (evts : Events) (_ : CandidateExecution evts) (r : SetRel Event Event) := SetRel.dom r

@[simp] def range (evts : Events) (_ : CandidateExecution evts) (r : SetRel Event Event) := SetRel.cod r

@[simp] def po_loc (evts : Events) (X : CandidateExecution evts) := X.po' ∩ CatRel.Rel.location

@[simp] def fre (evts : Events) (X : CandidateExecution evts) := X.fr' ∩ CatRel.Rel.external

@[simp] def fri (evts : Events) (X : CandidateExecution evts) := X.fr' ∩ CatRel.Rel.internal

@[simp] def rfe (evts : Events) (X : CandidateExecution evts) := X.rf' ∩ CatRel.Rel.external

@[simp] def rfi (evts : Events) (X : CandidateExecution evts) := X.rf' ∩ CatRel.Rel.internal

@[simp] def coe (evts : Events) (X : CandidateExecution evts) := X.co' ∩ CatRel.Rel.external

@[simp] def coi (evts : Events) (X : CandidateExecution evts) := X.co' ∩ CatRel.Rel.internal

@[simp] def int (evts : Events) (_ : CandidateExecution evts) := CatRel.Rel.internal

@[simp] def ext (evts : Events) (_ : CandidateExecution evts) := CatRel.Rel.external

end Std

open Std

[model| lkmm

enum Accesses = ONCE' ||
  RELEASE'  ||
  ACQUIRE'  ||
  NORETURN'  ||
  MB'
instructions {R, W, RMW}[Accesses]

enum Barriers = wmb'  ||
  rmb'  ||
  barrier'

instructions {F}[Barriers]

let FailedRMW = RMW \ (domain(rmw) | range(rmw))
let Acquire = ACQUIRE \ W \ FailedRMW
let Release = RELEASE \ R \ FailedRMW
let Mb = MB \ FailedRMW
let Noreturn = NORETURN \ W

let Marked = (~M) | IW | ONCE | RELEASE | ACQUIRE | MB | RMW

let Plain = M \ Marked

let strong_fence = mb

-- Acquire-Release
let acq_po = [Acquire] ; po ; [M]
let po_rel = [M] ; po ; [Release]

-- SCPV
let com = rf | co | fr
acyclic po_loc | com as coherence

-- Atomic Read-Modify-Write
empty rmw & (fre ; coe) as atomic

-- Preserved Program Order
let dep = addr | data
let rwdep = (dep | ctrl) ; [W]
let overwrite = co | fr
let to_w = rwdep | (overwrite & int) | (addr ; [Plain] ; wmb)
let to_r = addr | (dep ; [Marked] ; rfi)
let ppo = to_r | to_w | fence

let A_cumul(r) = (rfe ; [Marked])? ; r

let a = A_cumul(po_rel)

let cumul_fence = [Marked] ; (A_cumul(strong_fence | po_rel) | wmb) ; [Marked]
let prop = [Marked] ; (overwrite & ext)? ; cumul_fence* ; [Marked] ; (rfe)? ; [Marked]

-- Happends Before Relation
let hb = [Marked] ; (ppo | rfe | ((prop \ id) & int)) ; [Marked]

acyclic hb as happens_before

-- Propagation Before Relation
let pb = prop ; strong_fence ; hb* ; [Marked]
acyclic pb as propagation
]

[model| tso_x86

let xppo = ((W*W) | (R*W) | (R*R)) & po
let At = domain(rmw) | range(rmw)
let implied = po;[At | F] | [At | F];po
acyclic (implied | xppo | rfe | fr | co) as tso
]

[model| bpf
let po_amo_fetch = ([M];po;RMW) | (RMW;po;[M])

let load_acquire = ([lkmm.ACQUIRE];po;[M])
let store_release = ([M];po;[lkmm.RELEASE])
let rcpc = load_acquire | store_release

let addr_dep = [R];addr;[M]
let data_dep = [R];data;[W]
let ctrl_dep = [R];ctrl;[W]

let com = co | rf | fr

let ppo =
 po_amo_fetch | rcpc
| addr_dep
| data_dep
| ctrl_dep
| [M];(addr|data);[W];rfi;[R]
| [M];addr;[M];po;[W]
| (coi | fri)

let A-cumul = (rfe)? ; (po_amo_fetch | store_release)
let prop = (coe | fre)? ; A-cumul* ; (rfe)?

acyclic com | po-loc as Coherence

let hb = ppo | rfe | ((prop \ id) & int)

acyclic hb as Happens-before

let pb = prop ; po_amo_fetch ; hb*

-- acyclic pb as Propagation

-- empty rmw & (fre;coe) as Atomic

-- acyclic po_amo_fetch | com as fetch_fence
]

-- #reduce lkmm.A_cumul
