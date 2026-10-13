import ChessProof.Spec

namespace Chess

def pieceOfChar (ch : Char) : Option Piece :=
  let c := if ch.isUpper then Color.white else .black
  let k : Option Kind :=
    match ch.toLower with
    | 'p' => some .pawn
    | 'n' => some .knight
    | 'b' => some .bishop
    | 'r' => some .rook
    | 'q' => some .queen
    | 'k' => some .king
    | _ => none
  k.map fun k => ⟨c, k⟩

def parseRank (cs : List Char) (f : Nat) (acc : List (Nat × Piece)) : Option (List (Nat × Piece)) :=
  match cs with
  | [] => if f == 8 then some acc else none
  | ch :: rest =>
    if ch.isDigit then parseRank rest (f + (ch.toNat - '0'.toNat)) acc
    else do
      let pc ← pieceOfChar ch
      if f < 8 then parseRank rest (f + 1) ((f, pc) :: acc) else none

def parseBoard (s : String) : Option (Array (Option Piece)) := do
  let ranks := s.splitOn "/"
  if ranks.length != 8 then none
  let mut arr : Array (Option Piece) := Array.replicate 64 none
  for (rs, i) in ranks.zip (List.range 8) do
    let r := 7 - i
    for (f, pc) in ← parseRank rs.toList 0 [] do
      arr := arr.set! (r * 8 + f) (some pc)
  return arr

def parseSq (s : String) : Option Sq :=
  match s.toList with
  | [f, r] => if f.toNat < 'a'.toNat || r.toNat < '1'.toNat then none
    else mkSq (f.toNat - 'a'.toNat) (r.toNat - '1'.toNat)
  | _ => none

def parseFen (s : String) : Option Pos := do
  let fs := (s.splitOn " ").filter (· != "")
  let arr ← parseBoard (← fs[0]?)
  let turn ← match fs[1]? with
    | some "w" => some Color.white
    | some "b" => some Color.black
    | _ => none
  let cr := (fs[2]?.getD "-").toList
  let ep ← match fs[3]? with
    | none => some none
    | some "-" => some none
    | some t => (parseSq t).map some
  pure {
    board := fun q => arr.getD q.val none
    turn
    castleK := fun c => cr.contains (if c == .white then 'K' else 'k')
    castleQ := fun c => cr.contains (if c == .white then 'Q' else 'q')
    ep }

def sqName (s : Sq) : String :=
  (Char.ofNat ('a'.toNat + s.file)).toString ++ (Char.ofNat ('1'.toNat + s.rank)).toString

def kindChar : Kind → String
  | .pawn => "p"
  | .knight => "n"
  | .bishop => "b"
  | .rook => "r"
  | .queen => "q"
  | .king => "k"

def Move.uci (m : Move) : String :=
  sqName m.src ++ sqName m.dst ++ (m.promo.map kindChar).getD ""

end Chess
