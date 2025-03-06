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

MyNat : Set
MyNat = Nat

id : {A : Set} → A → A
id x = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = x

data List (A : Set) : Set where
    []   : List A
    _::_ : A → List A → List A

infixr 5 _::_

data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B
    
infixr 4 _,_

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y

length : {A : Set} → List A → Nat
length [] = zero
length (x :: xs) = suc (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys) 

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = (f x) :: (map f xs)  

data Maybe (A : Set) : Set where
    just : A → Maybe A
    nothing : Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup [] x = nothing
lookup (x :: xs) zero = just x
lookup (x :: xs) (suc v) = lookup xs v

