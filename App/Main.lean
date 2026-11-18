import LeanAID

def main (args : List String) : IO UInt32 := do
  IO.println s!"aid-lean: {args}"
  return 0
