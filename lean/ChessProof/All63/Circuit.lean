import Std.Data.HashMap
import ChessProof.Cnf

namespace Chess.All63

inductive Wire where
  | tt
  | ff
  | lit (l : Int)
deriving DecidableEq, Repr, Inhabited

def Wire.neg : Wire → Wire
  | .tt => .ff
  | .ff => .tt
  | .lit l => .lit (-l)

def Wire.eval (a : Assignment) : Wire → Bool
  | .tt => true
  | .ff => false
  | .lit l => litVal a l

inductive Ex where
  | k (b : Bool)
  | v (l : Int)
  | not (e : Ex)
  | and (es : List Ex)
  | or (es : List Ex)
deriving Inhabited

mutual
def Ex.eval (a : Assignment) : Ex → Bool
  | .k b => b
  | .v l => litVal a l
  | .not e => !e.eval a
  | .and es => Ex.evalAll a es
  | .or es => Ex.evalAny a es

def Ex.evalAll (a : Assignment) : List Ex → Bool
  | [] => true
  | e :: es => e.eval a && Ex.evalAll a es

def Ex.evalAny (a : Assignment) : List Ex → Bool
  | [] => false
  | e :: es => e.eval a || Ex.evalAny a es
end

inductive Fam where
  | gate
  | onehot
  | rank
  | start
  | ep
  | castle
  | material
  | allcheck
  | thr
deriving DecidableEq, Repr, Inhabited

inductive VDef where
  | x (q k : Nat)
  | ep (f : Nat)
  | cr (kside : Bool)
  | gate (isAnd : Bool) (L : List Int)
deriving DecidableEq, Repr, Inhabited

structure St where
  nv : Nat := 0
  cls : Array (Fam × Clause) := #[]
  cache : Std.HashMap (Bool × List Int) Nat := {}
  defs : Array VDef := #[]

abbrev M := StateM St

def newVar (d : VDef) : M Nat :=
  modifyGet fun s => (s.nv + 1, { s with nv := s.nv + 1, defs := s.defs.push d })

def emit (f : Fam) (c : Clause) : M Unit :=
  modify fun s => { s with cls := s.cls.push (f, c) }

def emitW (f : Fam) (ws : List Wire) : M Unit :=
  if ws.contains .tt then pure ()
  else emit f (ws.filterMap fun | .lit l => some l | _ => none).toArray

def require (f : Fam) (w : Wire) : M Unit := emitW f [w]

def dedupSorted : List Int → List Int
  | a :: b :: t => if a == b then dedupSorted (b :: t) else a :: dedupSorted (b :: t)
  | l => l

def normLits (ws : List Wire) : List Int :=
  dedupSorted ((ws.filterMap fun | .lit l => some l | _ => none).mergeSort fun a b => decide (a ≤ b))

def gateNew (isAnd : Bool) (L : List Int) : M Wire := do
  match (← get).cache[(isAnd, L)]? with
  | some g => return .lit g
  | none =>
    let g ← newVar (.gate isAnd L)
    let gi : Int := g
    if isAnd then
      for l in L do emit .gate #[-gi, l]
      emit .gate (#[gi] ++ (L.map (- ·)).toArray)
    else
      for l in L do emit .gate #[gi, -l]
      emit .gate (#[-gi] ++ L.toArray)
    modify fun s => { s with cache := s.cache.insert (isAnd, L) g }
    return .lit gi

def gate (isAnd : Bool) (ws : List Wire) : M Wire :=
  let absorb := if isAnd then Wire.ff else Wire.tt
  if ws.contains absorb then pure absorb
  else
    match normLits ws with
    | [] => pure absorb.neg
    | [l] => pure (.lit l)
    | L => if L.any (fun l => L.contains (-l)) then pure absorb else gateNew isAnd L

mutual
def compile : Ex → M Wire
  | .k b => pure (if b then .tt else .ff)
  | .v l => pure (.lit l)
  | .not e => do return (← compile e).neg
  | .and es => do gate true (← compileAll es)
  | .or es => do gate false (← compileAll es)

def compileAll : List Ex → M (List Wire)
  | [] => pure []
  | e :: es => do
    let w ← compile e
    let ws ← compileAll es
    pure (w :: ws)
end

def counterRow (l : Wire) (prev : Array Wire) : List Nat → Array Wire → M (Array Wire)
  | [], cur => pure cur
  | j :: js, cur => do
    let a ← gate true [l, prev[j - 1]!]
    let o ← gate false [prev[j]!, a]
    counterRow l prev js (cur.push o)

def counter (L : List Wire) (k : Nat) : M (Array Wire) :=
  L.foldlM (fun prev l => counterRow l prev (List.range' 1 k) #[.tt]) (#[.tt] ++ Array.replicate k .ff)

def atleast (f : Fam) (L : List Wire) (k : Nat) : M Unit := do
  let c ← counter L k
  require f c[k]!

def atmost (f : Fam) (L : List Wire) (k : Nat) : M Unit := do
  let c ← counter L (k + 1)
  require f c[k + 1]!.neg

def St.toCnf (s : St) : Cnf := ⟨s.nv, s.cls.map (·.2)⟩

end Chess.All63
