import ChessProof.All63.Trust
import ChessProof.C364.Trust

open Chess

def main (args : List String) : IO UInt32 := do
  match args with
  | [fam, i, out] =>
    let f := if fam == "63" then All63.G63 i.toNat! else C364.R364 i.toNat!
    let h ← IO.FS.Handle.mk out .write
    f.writeDimacs (IO.FS.Stream.ofHandle h)
    IO.println s!"wf {f.wfB}"
    return 0
  | [fam, i, _, prf] =>
    let f := if fam == "63" then All63.G63 i.toNat! else C364.R364 i.toNat!
    let bytes ← IO.FS.readBinFile prf
    let ok := f.lratBytesOk bytes
    IO.println s!"lratBytesOk {ok}"
    return if ok then 0 else 1
  | _ => IO.eprintln "usage: routea <63|364> <i> <cnf-out> [<lrat>]"; return 2
