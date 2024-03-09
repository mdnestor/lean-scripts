structure TuringMachine where /- generalizes to tapes besides ℤ obviously 💅 -/
  tape: Type
  symbol: Type
  state: Type
  shift: Type
  translate: tape × shift → tape
  update: state × symbol → state × symbol × shift

structure DynamicalSystem where
  state: Type
  update: state → state

def TuringMachineToDynamicalSystem (M: TuringMachine) [DecidableEq M.tape]: DynamicalSystem := {
  state := (M.tape → M.symbol) × M.state × M.tape
  update := fun (u, s, x) => by {
    have (y1, y2, y3) := M.update (s, (u x))
    exact (
      fun x0 => if x = x0 then y2 else (u x0),
      y1,
      M.translate (x, y3)
    )
  }
}

/- some theorem to cap it off? -/
