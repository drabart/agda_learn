data Nat : Set where
    zero : Nat
    suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}
    
_+_ : Nat → Nat → Nat
zero + y = y
(suc x) + y = suc (x + y)

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

data Vec (A : Set) : Nat → Set where
    [] : Vec A 0
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)


myVec1 : Vec Nat 5
myVec1  = 1 :: 2 :: 3 :: 4 :: 5 :: []

zeroes : (n : Nat) → Vec Nat n
zeroes zero = []
zeroes (suc n) = 0 :: (zeroes n)

downFrom : (n : Nat) → Vec Nat n
downFrom zero = []
downFrom (suc n) = n :: (downFrom n)

prepend : {n : Nat} → Bool → Vec Bool n → Vec Bool (suc n)
prepend b s = b :: s

_++Vec_ : {A : Set} {m n : Nat} → Vec A n → Vec A m → Vec A (n + m)
[] ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (x :: xs) = x

tail : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail (x :: xs) = xs

dotProduct : {n : Nat} → Vec Nat n → Vec Nat n → Nat
dotProduct [] [] = 0
dotProduct (x :: xs) (y :: ys) = (x * y) + dotProduct xs ys

data Fin : Nat → Set where
    zero : {n : Nat} → Fin (suc n)
    suc  : {n : Nat} → Fin n → Fin (suc n)

zero3 : Fin 3
zero3 = zero

lookupVec : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupVec (x :: xs) zero = x
lookupVec (x :: xs) (suc i) = lookupVec xs i

putVec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putVec zero v (x :: xs) = v :: xs
putVec (suc i) v (x :: xs) = x :: putVec i v xs

data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (x : A) → B x → Σ A B

_×'_ : (A B : Set) → Set
A ×' B = Σ A (λ _ → B)

pairToΣ : {A B : Set} → (A × B) → (A ×' B)
pairToΣ (x , y) = x , y

ΣToPair : {A B : Set} → (A ×' B) → (A × B)
ΣToPair (x , y) = x , y 

fstΣ : {A : Set} {B : A → Set} → Σ A B → A
fstΣ (x , y) = x

sndΣ : {A : Set} {B : A → Set} → (z : Σ A B) → B (fstΣ z)
sndΣ (x , y) = y

List' : (A : Set) → Set
List' A = Σ Nat (Vec A)

[]' : {A : Set} → List' A
[]' = 0 , []

_::'_ : {A : Set} → A → List' A → List' A
x ::' ys = suc (fstΣ ys) , (x :: (sndΣ ys))
infixr 5 _::'_

ListToList' : {A : Set} → List A → List' A
ListToList' [] = []'
ListToList' (x :: xs) = x ::' (ListToList' xs)

List'ToList : {A : Set} → List' A → List A
-- List'ToList (n , xs) = vecToList xs
List'ToList (0 , []) = []
List'ToList (suc n , x :: xs) = x :: List'ToList (n , xs)

data Either (A : Set) (B : Set) : Set where
    left : A → Either A B
    right : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left x) l r = l x 
cases (right x) l r = r x

data ⊤ : Set where
    tt : ⊤

data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

proof1 : {P : Set} → P → P
proof1 p = p

proof2 : {P Q R : Set} → (P → Q) × (Q → R) → (P → R)
proof2 (f , g) = λ x → g (f x)

proof3 : {P Q R : Set} → (Either P Q → R) → (P → R) × (Q → R)
proof3 f = (λ x → f (left x)) , (λ y → f (right y))

proof4 : {A B : Set} → A → (B → A)
proof4 x = λ _ → x

proof5 : {A : Set} → A × ⊤ → Either A ⊥
proof5 (x , tt) = left x

proof6 : {A B C : Set} → (A → B → C) → ((A × B) → C)
proof6 f (x , y) = (f x) y 

proof7 : {A B C : Set} → (A × (Either B C)) → Either (A × B) (A × C)
proof7 (a , left x) = left (a , x)
proof7 (a , right x) = right (a , x)

proof8 : {A B C D : Set} → (A → C) × (B → D) → ((A × B) → (C × D))
proof8 (ac , bd) (x , y) = (ac x , bd y) 
  
proof85 : {P : Set} → (⊤ → ⊥) → ⊥
proof85 f = f tt

proof9 : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
proof9 f = {! f (right (λ x → x x)) !} 