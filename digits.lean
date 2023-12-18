

/--
 Computes the decimal digits of a natural number, in little-endian order.
 -/
def decimalDigits : Nat → List Nat
| 0 => []
| n + 1 => ((n + 1) % 10 :: decimalDigits ((n + 1) / 10))
decreasing_by exact
  Nat.div_lt_self (Nat.succ_pos n) (Nat.succ_lt_succ (Nat.succ_pos 8))

--#reduce decimalDigits 1234

def main (args: List String) : IO Unit := do
  let n := (args.get! 0).toNat!
  IO.println (decimalDigits n)

-- #eval decimalDigits 1234567890

def decimalDigitsWithFuel : Nat → Nat → List Nat
|     0, _ => []
|     _, 0 => []
| m + 1, n => (n % 10 :: decimalDigitsWithFuel m (n / 10))

def decimalDigits' (x : Nat) : List Nat := decimalDigitsWithFuel x x

--#reduce decimalDigits' 1234
#print decimalDigits

#check Or.rec
#check Or.recOn

