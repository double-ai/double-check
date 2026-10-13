import ChessProof.Spec
import ChessProof.All63.Enc
import ChessProof.All63.Admissible

namespace Chess.All63

def kindIdx : Kind → Nat
  | .pawn => 0
  | .knight => 1
  | .bishop => 2
  | .rook => 3
  | .queen => 4
  | .king => 11

def symOf : Option Piece → Nat
  | none => EMP
  | some ⟨.white, k⟩ => kindIdx k
  | some ⟨.black, k⟩ => kindIdx k + 5

def VDef.val (p : Pos) (A : Assignment) : VDef → Bool
  | .x q k => symOf (p.board (toSq q)) == k
  | .ep f => p.ep == some (toSq (f + 40))
  | .cr ks => if ks then p.castleK .white else p.castleQ .white
  | .gate isAnd L => if isAnd then L.all (litVal A) else L.any (litVal A)

def Good (p : Pos) (A : Assignment) (s : St) : Prop :=
  ∀ i (h : i < s.defs.size), A (i + 1) = s.defs[i].val p A

def valsOf (p : Pos) (defs : Array VDef) : Array Bool :=
  defs.foldl (fun acc d => acc.push (d.val p fun v => if v = 0 then false else acc.getD (v - 1) false)) #[]

def assign (p : Pos) (s : St) : Assignment :=
  let vs := valsOf p s.defs
  fun v => if v = 0 then false else vs.getD (v - 1) false

def cfgOf (p : Pos) : Cfg := ⟨(kingSq p .white).val, (kingSq p .black).val, inCheck p .white⟩

def Fits (c : Cfg) (p : Pos) : Prop := Admissible p ∧ p.turn = .white ∧ cfgOf p = c

def Cand.covers (m : Cand) : List Move :=
  if m.w = 4 then [Kind.knight, .bishop, .rook, .queen].map fun k => ⟨toSq m.src, toSq m.dst, some k⟩
  else if m.w = 1 then [m.mv] else []

end Chess.All63
