import ChessProof.Spec
import ChessProof.Fen

open Chess

def perft (p : Pos) : Nat → Nat
  | 0 => 1
  | 1 => (legalMoves p).length
  | n + 2 => (legalMoves p).foldl (fun a m => a + perft (play p m) (n + 1)) 0

def movesLine (p : Pos) : String :=
  " ".intercalate ((legalMoves p).map fun m => m.uci ++ (if givesCheck p m then "+" else ""))

def replay : Pos → List String → Option Pos
  | p, [] => some p
  | p, u :: us => ((legalMoves p).find? fun m => m.uci == u).bind fun m => replay (play p m) us

def trace : Pos → List String → List String → Option (List String)
  | p, [], acc => some (movesLine p :: acc).reverse
  | p, u :: us, acc => ((legalMoves p).find? fun m => m.uci == u).bind fun m => trace (play p m) us (movesLine p :: acc)

def handle (line : String) : String :=
  match line.splitOn " " with
  | "game" :: us =>
    match trace initial (us.filter (· != "")) [] with
    | some ls => "ok " ++ " | ".intercalate ls
    | none => "err"
  | "line" :: us =>
    match replay initial (us.filter (· != "")) with
    | some p => "ok " ++ movesLine p
    | none => "err"
  | "moves" :: rest =>
    match parseFen (" ".intercalate rest) with
    | some p => "ok " ++ movesLine p
    | none => "err"
  | "perft" :: d :: rest =>
    match d.toNat?, (if rest.isEmpty then some initial else parseFen (" ".intercalate rest)) with
    | some n, some p => "ok " ++ toString (perft p n)
    | _, _ => "err"
  | _ => "err"

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let l := String.ofList (line.toList.filter fun c => c != '\n' && c != '\r')
  o.putStrLn (handle l)
  o.flush
  loop h o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
