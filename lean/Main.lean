import OnlineMatching.Final

/-! Command-line entry point: reads a graph from stdin and prints `Final.opt`. -/

def readEdges : List Nat → Except String (List OnlineMatching.Offline.Edge)
  | [] => .ok []
  | u :: v :: rest => do
      return (min u v, max u v) :: (← readEdges rest)
  | _ => .error "Expected pairs of edge endpoints"

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let tokens := ((input.replace "\n" " ").replace "\r" " ").replace "\t" " "
  let numbers ← (tokens.splitOn " ").filter (· != "") |>.mapM fun token =>
    match token.toNat? with
    | some n => pure n
    | none => throw (IO.userError s!"Invalid integer: {token}")
  let n :: m :: rest := numbers | throw (IO.userError "Expected n m and m edges")
  let edges ← match readEdges rest with
    | .ok es => pure es
    | .error message => throw (IO.userError message)
  if edges.length != m || m == 0 || !edges.Nodup ||
      !edges.all (fun (u,v) => u < v && v < n) then
    throw (IO.userError "Expected a nonempty simple graph on vertices 0..n-1")
  let result := OnlineMatching.Final.opt n edges
  (← IO.getStdout).putStrLn s!"{result.num}/{result.den}"
