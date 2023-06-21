module Z3

type z3 = {
  from_z3: unit -> ML string;
  to_z3: string -> ML unit;
}

val with_z3
  (#a: Type)
  (f: (z3 -> ML a))
: ML a
