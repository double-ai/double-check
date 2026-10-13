import ChessProof.Trust
import ChessProof.All63.Enc
import ChessProof.All63.Cases

namespace Chess.All63

def G63 (i : Nat) : Cnf := G (caseAt i)

def UnsatFacts : Prop := UnsatFamily 7224 G63

theorem routeA_case (i : Nat) (bytes : ByteArray) (h : (G63 i).lratBytesOk bytes = true) : (G63 i).Unsat :=
  (G63 i).unsat_of_lratBytesOk bytes h

theorem routeA_facts (r : RouteA 7224 G63) : UnsatFacts := r.family

end Chess.All63
