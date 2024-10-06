@[simp] def int_shift := 1
@[simp] def char_shift := 2
@[simp] def val_true := 3
@[simp] def val_false := 7
@[simp] def val_void := 15

@[simp] def type_char := 1
@[simp] def type_int := 0

@[simp] def int_mask := 1
@[simp] def char_mask := 3

class Convertible (α : Type) where
  valToBits : α → Nat

@[simp] instance : Convertible Nat where
  valToBits v := v <<< int_shift

@[simp] instance : Convertible Bool where
  valToBits : Bool -> Nat
  | true => val_true
  | false => val_false

@[simp] instance : Convertible Char where
  valToBits v := ((Char.toNat v) <<< char_shift) ||| type_char
