data Nat : Set where
    zero : Nat
    suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}
    
_+_ : Nat → Nat → Nat
zero + y = y
(suc x) + y = x + (suc y)

halve : Nat → Nat
halve (suc(suc x)) = (suc zero) + (halve x)
halve (suc x) = zero
halve zero = zero

_*_ : Nat → Nat → Nat
zero * y = zero
suc(x) * y = y + (x * y)

data Bool : Set where
    true : Bool
    false : Bool

not : Bool → Bool
not true = false
not false = true

_&&_ : Bool → Bool → Bool
true && true = true
a && b = false

_||_ : Bool → Bool → Bool
false || false = false
a || b = true


