import Yatima

def edges: List (String × String) :=
  [ ("A", "B"), 
    ("A", "C"), 
    ("A", "D"), 
    ("B", "C"), 
    ("B", "D"), 
    ("C", "D"),
    ("C", "A"),
    ("D", "D")
  ]

def main : IO Unit := do
  let g : Graph String := .buildG edges
  IO.println s!"vertices: {g.vertices}"
  IO.println s!"edges: {g.edges}"
  let gs := Graph.scc? g
  IO.println s!"scc?: {gs}"
