import Yatima.Compiler.Utils
import Yatima.ForStdLib

/-
This graph API needs work beforing being factored out because it's specific to
Lean types.

Another point: we'll soon drop the need for this API once we migrate to an
updated toolchain.
-/

variable [Ord α]

open Std (RBMap) in
structure Graph (α : Type) [Ord α] where
  data : Std.RBMap α (List α) compare

open Lean Std
namespace Graph

def empty: Graph α := { data := Std.RBMap.empty }

def vertices(g : Graph α): List α :=
  g.data.toList.map Prod.fst

def edges(g : Graph α) : List (α × α) := 
  (g.data.toList.map fun (x, xs) => xs.map fun y => ⟨x, y⟩).join

def buildG(edges : List (α × α)) : Graph α :=
  List.foldl (fun g e => 
    -- add the edge source as a vertex
    let g1 : Graph α := match g.data.find? e.1 with 
    | some v => { data := g.data.insert e.1 $ e.2 :: v }
    | none =>   { data := g.data.insert e.1 [e.2] }
    -- add the edge target as a vertex
    { g1 with data := g1.data.insert e.2 $ List.flatten (g1.data.find? e.2) }
  ) empty edges

def reverseE(g : Graph α) : List (α × α) :=
  g.edges.map fun (v, w) => (w, v)

def transposeG(g : Graph α) : Graph α :=
  buildG g.reverseE

open Std in 
def outDegrees(g : Graph α) : RBMap α Nat compare :=
  RBMap.fromList (g.data.toList.map fun (x, xs) => (x, xs.length)) compare

def outDegree(g : Graph α) (v : α) : Option Nat :=
  List.length <$> g.data.find? v

open Std in 
def inDegrees(g : Graph α) : RBMap α Nat compare :=
  g.data.fold (fun degrees _ xs => 
    xs.foldl (fun acc v => 
      match acc.find? v with 
      | some n => acc.insert v (n + 1)
      | none => acc.insert v 1
    ) degrees
  ) RBMap.empty

open Std in 
/-- Not sure which one is better? -/
def inDegrees'(g : Graph α) : RBMap α Nat compare :=
  g.transposeG.outDegrees

/-- Don't use this, it will recompute `g.inDegrees` every time, yuck! -/
def inDegree(g : Graph α) (v : α) : Option Nat :=
  g.inDegrees.find? v

structure dfsState (α) [Ord α] where 
  visited : RBMap α Bool compare

abbrev dfsM (α) [Ord α] := ReaderT (Graph α) $ EStateM String (dfsState α)

open YatimaStdLib (Tree)

partial def generate [ToString α] (v : α) : (dfsM α) $ (Tree α) := do
  match (← get).visited.find? v with
  | some _ => pure .empty
  | none => do
    set { ← get with visited := (← get).visited.insert v true }
    match (← read).data.find? v with 
    | some vs => do
      let ts ← vs.mapM generate
      pure $ .node v $ ts.filter $ not ∘ Tree.isEmpty
    | none => throw s!"Vertex {v} not found in graph"

def generateVs [ToString α] (vs : List α) : (dfsM α) $ List $ Tree α := do 
  vs.mapM generate

def dfsM.run [ToString α] (g : Graph α) (v : α) : Except String $ Tree α  :=
  match EStateM.run (ReaderT.run (generate v) g) { visited := .empty } with 
  | .ok res _ => .ok res 
  | .error e _ => .error e

def dfs? [ToString α] (g : Graph α) (vs : List α) : Except String $ List $ Tree α :=
  match EStateM.run (ReaderT.run (generateVs vs) g) { visited := .empty } with 
  | .ok res _ => .ok res 
  | .error e _ => .error e

def dfs! [ToString α] (g : Graph α) (vs : List α) : List $ Tree α :=
  match EStateM.run (ReaderT.run (generateVs vs) g) { visited := .empty } with 
  | .ok res _ => res 
  | .error e _ => panic! e

def dff? [ToString α] (g : Graph α) : Except String $ List $ Tree α :=
  g.dfs? g.vertices 

def dff! [ToString α] (g : Graph α) : List $ Tree α :=
  g.dfs! g.vertices

def preord [ToString α] (g : Graph α) : List α :=
  Tree.preorderF g.dff!

def postord [ToString α] (g : Graph α) : List α :=
  Tree.postorderF (dff! g)

structure NodeInfo where
  index : Nat
  lowlink : Nat
  onStack : Bool
  deriving Repr

instance : ToString NodeInfo :=
  { toString := fun info => s!"i: {info.index}, low: {info.lowlink}, on: {info.onStack}" }

structure sccState (α) [Ord α] where 
  info : RBMap α NodeInfo compare
  index : Nat 
  stack : List α

instance : Inhabited (sccState α):= 
  { default := ⟨.empty, default, default⟩ }

abbrev sccM (α) [Ord α] [ToString α] := ReaderT (Graph α) $ EStateM String (sccState α)

namespace sccM

def getInfo [ToString α] (v : α) : (sccM α) NodeInfo := do 
  (← get).info.findM v s!"Vertex {v} not found in graph" 

def setInfo [ToString α]  (v : α) (info : NodeInfo) : (sccM α) Unit := do
  set { ← get with info := (← get).info.insert v info }

/--  
`strongConnect v` returns all the strongly connected components
of the graph `G` (encoded in the `ReaderT` of the `sccM` monad)
that can be found by depth first searching from `v`.

Note that `G` is not necessarily simple, i.e. it may have self loops,
and we consider those singletons as strongly connected to itself.
-/
partial def strongConnect [BEq α] [ToString α] (v : α) : (sccM α) (List $ (List α)) := do 
  let idx := (← get).index
  set ({ info := (← get).info.insert v ⟨idx, idx, true⟩, 
         index := idx + 1, 
         stack := v :: (← get).stack } : sccState α)
  
  let edges ← match (← read).data.find? v with 
              | some vs => pure vs
              | none => throw s!"Vertex {v} not found in graph"
  
  let mut sccs := []
  let mut vll := idx 
  for w in edges do 
    match (← get).info.find? w with 
    | some ⟨widx, _, won⟩ => do 
      if won then
        vll := min vll widx
    | none => do
      sccs := (← strongConnect w) ++ sccs
      let ⟨_, wlowlink, _⟩ ← getInfo w
      vll := min vll wlowlink

  setInfo v ⟨idx, vll, true⟩
  
  if idx == vll then do
    let s := (← get).stack
    let (scc, s) := s.splitAtP fun w => w != v 
    scc.forM fun w => do 
      let ⟨idx, lowlink, _⟩ ← getInfo w
      setInfo w ⟨idx, lowlink, false⟩
    set { ← get with stack := s } 
    -- if `scc` has length 1, check if `v` has a self-loop
    if scc.length >= 2 || scc.length == 1 && edges.contains v then 
      pure $ scc::sccs
    else
      pure $ sccs
  else pure sccs

def run [BEq α] [ToString α] [ToString α] : (sccM α) $ List $ (List α) := do 
  (← read).vertices.foldlM (init := []) $ fun acc v => do
    match (← get).info.find? v with 
    | some ⟨_, _, _⟩ => pure acc 
    | none => 
    match ← strongConnect v with 
      | [] => pure $ acc
      | as => pure $ as ++ acc

end sccM

def scc? [BEq α] [ToString α] (g : Graph α) : Except String $ List $ (List α) :=
  match EStateM.run (ReaderT.run sccM.run g) default with 
  | .ok  res _ => .ok res 
  | .error e _ => .error e

def scc! [BEq α] [ToString α] (g : Graph α) : List $ (List α) :=
  match EStateM.run (ReaderT.run sccM.run g) default with 
  | .ok  res _ => res 
  | .error e _ => panic! e

end Graph
