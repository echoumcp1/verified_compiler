def int_shift := 1
def char_shift := 2
def val_true := 3
def val_false := 7
def val_void := 15

def type_char := 1
def type_int := 0

def int_mask := 1
def char_mask := 3

class Convertible (α : Type) where
  valToBits : α → Nat

instance : Convertible Nat where
  valToBits v := v <<< int_shift

instance : Convertible Bool where
  valToBits : Bool -> Nat
  | true => val_true
  | false => val_false

instance : Convertible Char where
  valToBits v := ((Char.toNat v) <<< char_shift) ||| type_char
