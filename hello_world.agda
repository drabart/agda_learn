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
proof9 f = f (right (λ p → f (left p))) 

data IsEven : Nat → Set where
    zeroIsEven : IsEven zero
    sucsucIsEven : {n : Nat} → IsEven n → IsEven (suc (suc n))

6-is-even : IsEven 6
6-is-even = sucsucIsEven(sucsucIsEven(sucsucIsEven zeroIsEven))

7-is-not-even : IsEven 7 → ⊥
7-is-not-even (sucsucIsEven(sucsucIsEven(sucsucIsEven())))

data IsTrue : Bool → Set where
    TrueIsTrue : IsTrue true

_=Nat_ : Nat → Nat → Bool
zero    =Nat zero    = true
(suc x) =Nat (suc y) = x =Nat y
_       =Nat _       = false

length-is-3 : IsTrue(length (1 :: 2 :: 3 :: []) =Nat 3)
length-is-3 = TrueIsTrue

double : Nat → Nat
double zero     = zero
double (suc n)  = suc (suc (double n))

double-is-even : (n : Nat) → IsEven(double n)
double-is-even zero     = zeroIsEven
double-is-even (suc m)  = sucsucIsEven (double-is-even m)

n-equals-n : (n : Nat) → IsTrue (n =Nat n)
n-equals-n zero     = TrueIsTrue
n-equals-n (suc m)  = n-equals-n m

data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x
    
infix 4 _≡_

one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

zero-not-one : 0 ≡ 1 → ⊥
zero-not-one ()

id-returns-input : {A : Set} → (x : A) → id x ≡ x
id-returns-input x = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A}
    → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix 1 begin_
infix 3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

[_] : {A : Set} → A → List A
[ x ] = x :: []

reverse : {A : Set} → List A → List A
reverse []      = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-singleton : {A : Set} (x : A) → reverse [ x ] ≡ [ x ]
reverse-singleton x =
    begin
        reverse [ x ]
    =⟨⟩
        reverse [] ++ [ x ]
    =⟨⟩
        [] ++ [ x ]
    =⟨⟩
        [ x ]
    end

