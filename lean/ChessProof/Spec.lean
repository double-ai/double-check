namespace Chess

inductive Color where
  | white
  | black
deriving DecidableEq, Repr, Inhabited

def Color.opp : Color → Color
  | white => black
  | black => white

inductive Kind where
  | pawn
  | knight
  | bishop
  | rook
  | queen
  | king
deriving DecidableEq, Repr, Inhabited

structure Piece where
  color : Color
  kind : Kind
deriving DecidableEq, Repr, Inhabited

abbrev Sq := Fin 64

def Sq.file (s : Sq) : Nat := s.val % 8

def Sq.rank (s : Sq) : Nat := s.val / 8

def mkSq (f r : Nat) : Option Sq :=
  if h : f < 8 ∧ r < 8 then some ⟨r * 8 + f, by omega⟩ else none

def sq (f r : Nat) : Sq := ⟨(r * 8 + f) % 64, Nat.mod_lt _ (by decide)⟩

def off (s : Sq) (df dr : Int) : Option Sq :=
  let f := (s.file : Int) + df
  let r := (s.rank : Int) + dr
  if 0 ≤ f ∧ 0 ≤ r then mkSq f.toNat r.toNat else none

def allSq : List Sq := List.finRange 64

abbrev Board := Sq → Option Piece

structure Pos where
  board : Board
  turn : Color
  castleK : Color → Bool
  castleQ : Color → Bool
  ep : Option Sq

structure Move where
  src : Sq
  dst : Sq
  promo : Option Kind
deriving DecidableEq, Repr, Inhabited

def Color.fwd : Color → Int
  | white => 1
  | black => -1

def Color.home : Color → Nat
  | white => 0
  | black => 7

def Color.pawnHome : Color → Nat
  | white => 1
  | black => 6

def Color.last : Color → Nat
  | white => 7
  | black => 0

def knightD : List (Int × Int) := [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

def rookD : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1)]

def bishopD : List (Int × Int) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]

def queenD : List (Int × Int) := rookD ++ bishopD

def empty (b : Board) (t : Sq) : Bool := (b t).isNone

def steps (s : Sq) (ds : List (Int × Int)) : List Sq :=
  ds.filterMap fun (df, dr) => off s df dr

def ray (b : Board) (s : Sq) (df dr : Int) : Nat → List Sq
  | 0 => []
  | n + 1 =>
    match off s df dr with
    | none => []
    | some t => if empty b t then t :: ray b t df dr n else [t]

def rays (b : Board) (s : Sq) (ds : List (Int × Int)) : List Sq :=
  ds.flatMap fun (df, dr) => ray b s df dr 7

def attacks (b : Board) (s : Sq) (p : Piece) : List Sq :=
  match p.kind with
  | .pawn => steps s [(1, p.color.fwd), (-1, p.color.fwd)]
  | .knight => steps s knightD
  | .king => steps s queenD
  | .bishop => rays b s bishopD
  | .rook => rays b s rookD
  | .queen => rays b s queenD

def attacked (b : Board) (s : Sq) (c : Color) : Bool :=
  allSq.any fun t =>
    match b t with
    | some p => p.color == c && (attacks b t p).contains s
    | none => false

def inCheck (p : Pos) (c : Color) : Bool :=
  allSq.any fun t => p.board t == some ⟨c, .king⟩ && attacked p.board t c.opp

def foe (b : Board) (c : Color) (t : Sq) : Bool :=
  match b t with
  | some q => q.color != c
  | none => false

def epCap (p : Pos) (c : Color) (t : Sq) : Bool :=
  p.ep == some t && empty p.board t &&
    match off t 0 (-c.fwd) with
    | some u => p.board u == some ⟨c.opp, .pawn⟩
    | none => false

def pawnMoves (p : Pos) (s : Sq) (c : Color) : List Move :=
  let b := p.board
  let mk (t : Sq) : List Move :=
    if t.rank == c.last then [Kind.knight, .bishop, .rook, .queen].map fun k => ⟨s, t, some k⟩
    else [⟨s, t, none⟩]
  let one := (off s 0 c.fwd).filter (empty b)
  let two := if s.rank == c.pawnHome && one.isSome then (off s 0 (2 * c.fwd)).filter (empty b) else none
  let caps := (steps s [(1, c.fwd), (-1, c.fwd)]).filter fun t => foe b c t || epCap p c t
  (one.toList ++ caps).flatMap mk ++ two.toList.map fun t => ⟨s, t, none⟩

def pieceMoves (p : Pos) (s : Sq) (q : Piece) : List Move :=
  match q.kind with
  | .pawn => pawnMoves p s q.color
  | _ => ((attacks p.board s q).filter fun t => !(p.board t).any (·.color == q.color)).map fun t => ⟨s, t, none⟩

def castleMoves (p : Pos) : List Move :=
  let b := p.board
  let c := p.turn
  let r := c.home
  let e := sq 4 r
  let safe (f : Nat) := !attacked b (sq f r) c.opp
  let free (fs : List Nat) := fs.all fun f => empty b (sq f r)
  if b e == some ⟨c, .king⟩ && safe 4 then
    (if p.castleK c && b (sq 7 r) == some ⟨c, .rook⟩ && free [5, 6] && safe 5 then [⟨e, sq 6 r, none⟩] else []) ++
    (if p.castleQ c && b (sq 0 r) == some ⟨c, .rook⟩ && free [1, 2, 3] && safe 3 then [⟨e, sq 2 r, none⟩] else [])
  else []

def pseudo (p : Pos) : List Move :=
  allSq.flatMap (fun s =>
    match p.board s with
    | some q => if q.color == p.turn then pieceMoves p s q else []
    | none => []) ++ castleMoves p

def play (p : Pos) (m : Move) : Pos :=
  let b := p.board
  let isK := (b m.src).any (·.kind == .king)
  let isP := (b m.src).any (·.kind == .pawn)
  let rk := m.src.rank
  let rook : Option (Sq × Sq) :=
    if isK && m.src.file + 2 == m.dst.file then some (sq 7 rk, sq 5 rk)
    else if isK && m.dst.file + 2 == m.src.file then some (sq 0 rk, sq 3 rk)
    else none
  let victim : Option Sq :=
    if isP && m.src.file != m.dst.file && empty b m.dst then some (sq m.dst.file rk) else none
  let moved : Option Piece :=
    match m.promo with
    | some k => (b m.src).map fun q => ⟨q.color, k⟩
    | none => b m.src
  let touched (s : Sq) : Bool := m.src == s || m.dst == s
  { board := fun s =>
      if s == m.dst then moved
      else if s == m.src || victim == some s then none
      else
        match rook with
        | some (a, d) => if s == d then b a else if s == a then none else b s
        | none => b s
    turn := p.turn.opp
    castleK := fun c => p.castleK c && !touched (sq 4 c.home) && !touched (sq 7 c.home)
    castleQ := fun c => p.castleQ c && !touched (sq 4 c.home) && !touched (sq 0 c.home)
    ep :=
      if isP && (m.src.rank + 2 == m.dst.rank || m.dst.rank + 2 == m.src.rank) then
        some (sq m.src.file ((m.src.rank + m.dst.rank) / 2))
      else none }

def legalMoves (p : Pos) : List Move :=
  (pseudo p).filter fun m => !inCheck (play p m) p.turn

def givesCheck (p : Pos) (m : Move) : Bool :=
  inCheck (play p m) p.turn.opp

def backRank : List Kind := [.rook, .knight, .bishop, .queen, .king, .bishop, .knight, .rook]

def initial : Pos where
  board s :=
    match s.rank with
    | 0 => some ⟨.white, backRank.getD s.file .pawn⟩
    | 1 => some ⟨.white, .pawn⟩
    | 6 => some ⟨.black, .pawn⟩
    | 7 => some ⟨.black, backRank.getD s.file .pawn⟩
    | _ => none
  turn := .white
  castleK _ := true
  castleQ _ := true
  ep := none

inductive Reachable : Pos → Prop
  | init : Reachable initial
  | step {p : Pos} {m : Move} : Reachable p → m ∈ legalMoves p → Reachable (play p m)

def IsCheckSeq : Pos → List Move → Prop
  | _, [] => True
  | p, m :: ms => m ∈ legalMoves p ∧ givesCheck p m = true ∧ IsCheckSeq (play p m) ms

end Chess
