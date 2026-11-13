import PyCore.Cli
import Surf.Cli
import Surf.Run
import Surf.RunCore

/-- `pycore [FILE]`: read a program `(module ...)` or a pair `(pair (module ...) (sites ...))`
from FILE or standard input and print classifications, kinds, and the footprint.
`pycore surf [FILE]`: read Surf programs `(Module ...)` and print, for each, the
classifications and kinds computed on Surf and through the translation.
`pycore run [FILE]`: run Surf programs on test inputs with the reference
interpretation (`Surf/Run.lean`).
`pycore runcore [FILE]`: run them by Surf.Sem and by PyCore on their translation, and
compare the outcomes and the interpretation's traces (`Surf/RunCore.lean`). -/
def main (args : List String) : IO UInt32 := do
  let (cmd, args) := match args with
    | "surf" :: rest => ("surf", rest)
    | "run" :: rest => ("run", rest)
    | "runcore" :: rest => ("runcore", rest)
    | _ => ("", args)
  let input ← match args with
    | [file] => IO.FS.readFile file
    | _ => (← IO.getStdin).readToEnd
  let r := match cmd with
    | "surf" => Surf.Cli.runAll input
    | "run" => Surf.Run.runAll input
    | "runcore" => Surf.RunCore.runAll input
    | _ => PyCore.Cli.runInput input
  match r with
  | .ok lines => lines.forM (IO.println ·); return 0
  | .error e => IO.eprintln s!"error: {e}"; return 1
