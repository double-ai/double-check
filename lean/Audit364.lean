import ChessProof.C364.Trust

open Chess Chess.C364

def main (args : List String) : IO UInt32 := do
  match args with
  | ["count"] =>
    IO.println s!"{certRecords.length}"
    return 0
  | out :: idx =>
    let rs := certRecords.toArray
    for i in idx.map String.toNat! do
      let f := (rs.getD i default).formula.toCnf
      let h ← IO.FS.Handle.mk s!"{out}.{i}" .write
      f.writeDimacs (IO.FS.Stream.ofHandle h)
      IO.println s!"{i} {f.wfB}"
    return 0
  | _ => IO.eprintln "usage"; return 1
