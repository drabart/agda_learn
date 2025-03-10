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

not-not : (b : Bool) → not (not b) ≡ b
not-not false =
    begin
        not (not false)
    =⟨⟩
        not true
    =⟨⟩
        false
    end
not-not true =
    begin
        not (not true)
    =⟨⟩
        not false
    =⟨⟩
        true
    end

add-n-zero : (n : Nat) → n + zero ≡ n
add-n-zero zero = 
    begin
        zero + zero
    =⟨⟩ 
        zero
    end
add-n-zero (suc x) = 
    begin
        (suc x) + zero
    =⟨⟩
        suc (x + zero)
    =⟨ cong suc (add-n-zero x) ⟩
        suc x
    end

add-m-n : (m : Nat) → (n : Nat) → m + (suc n) ≡ suc(m + n)
add-m-n zero n = 
    begin
        zero + suc n
    =⟨⟩
        suc n
    =⟨⟩
        suc (zero + n)
    end
add-m-n (suc m) n = 
    begin
        (suc m) + suc n
    =⟨⟩
        suc (m + suc n)
    =⟨ cong suc (add-m-n m n) ⟩
        suc (suc (m + n))
    end

mn-equal-nm : (m : Nat) → (n : Nat) → m + n ≡ n + m
mn-equal-nm zero zero =
    begin
        zero + zero
    =⟨⟩
        zero + zero
    end
mn-equal-nm zero (suc n) =
    begin
        zero + (suc n)
    =⟨⟩
        suc (zero + n)
    =⟨ cong suc (mn-equal-nm zero n) ⟩
        suc (n + zero)
    =⟨⟩
        suc n + zero
    end
mn-equal-nm (suc m) zero =
    begin
        suc m + zero
    =⟨⟩
        suc (m + zero)
    =⟨ cong suc (mn-equal-nm m zero) ⟩
        suc (zero + m)
    =⟨⟩
        zero + suc m
    end
mn-equal-nm (suc m) (suc n) =
    begin
        suc m + suc n
    =⟨⟩
        suc (m + suc n)
    =⟨ cong suc (add-m-n m n)⟩
        suc (suc (m + n))
    =⟨ cong (λ x → suc (suc x)) (mn-equal-nm m n) ⟩ 
        suc (suc (n + m))
    =⟨⟩
        suc (suc n + m)
    =⟨ cong suc (sym (add-m-n n m)) ⟩
        suc (n + suc m)
    =⟨⟩
        (suc n) + (suc m)
    end

add-assoc : (x y z : Nat) → x + (y + z) ≡ (x + y) + z
add-assoc zero y z =
    begin
        zero + (y + z)
    =⟨⟩ -- applying the outer +
        y + z
    =⟨⟩ -- unapplying add
        (zero + y) + z
    end
add-assoc (suc x) y z =
    begin
        (suc x) + (y + z)
    =⟨⟩ -- applying the outer add
        suc (x + (y + z))
    =⟨ cong suc (add-assoc x y z) ⟩ -- using induction hypothesis
        suc ((x + y) + z)
    =⟨⟩ -- unapplying the outer add
        (suc (x + y)) + z
    =⟨⟩ -- unapplying the inner add
        ((suc x) + y) + z
    end

replicate : {A : Set}
    → Nat → A → List A
replicate zero x = []
replicate (suc n) x =
    x :: replicate n x

replicate-length-check : {A : Set} → (n : Nat) → (x : A) → (length (replicate n x)) ≡ n
replicate-length-check zero x =
    begin
        length (replicate zero x)
    =⟨⟩
        zero
    end
replicate-length-check (suc n) x =
    begin
        length (replicate (suc n) x)
    =⟨⟩
        1 + length (replicate n x)
    =⟨ cong (λ x → 1 + x) (replicate-length-check n x) ⟩
        1 + n
    end

append-assoc : {A : Set} → (xs ys zs : List A)
    → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
append-assoc [] ys zs =
    begin
        ([] ++ ys) ++ zs
    =⟨⟩
        [] ++ (ys ++ zs)
    end
append-assoc (x :: xs) ys zs =
    begin
        ((x :: xs) ++ ys) ++ zs
    =⟨⟩
        x :: (xs ++ ys) ++ zs
    =⟨ cong (λ y → x :: y) (append-assoc xs ys zs) ⟩
        x :: xs ++ (ys ++ zs)
    =⟨⟩
        (x :: xs) ++ (ys ++ zs)
    end

append-[] : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
append-[] [] =
    begin
        [] ++ []
    =⟨⟩
        []
    end 
append-[] (x :: xs) =
    begin
        (x :: xs) ++ []
    =⟨⟩
        x :: (xs ++ [])
    =⟨ cong (λ y → (x :: y)) (append-[] xs) ⟩
        (x :: xs)
    end

reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse [] =
    begin
        reverse (reverse [])
    =⟨⟩ -- applying inner reverse
        reverse []
    =⟨⟩ -- applying reverse
        []
    end
reverse-reverse (x :: xs) =
    begin
        reverse (reverse (x :: xs))
    =⟨⟩ -- applying the inner reverse
        reverse (reverse xs ++ [ x ])
    =⟨ reverse-distributivity (reverse xs) [ x ] ⟩ -- distributivity (see below)
        reverse [ x ] ++ reverse (reverse xs)
    =⟨⟩ -- reverse singleton list
        [ x ] ++ reverse (reverse xs)
    =⟨⟩ -- definition of ++
        x :: reverse (reverse xs)
    =⟨ cong (x ::_) (reverse-reverse xs) ⟩ -- using induction hypothesis
        x :: xs
    end
    where
        reverse-distributivity : {A : Set} → (xs ys : List A)
            → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
        reverse-distributivity [] ys =
            begin
                reverse ([] ++ ys)
            =⟨⟩ -- applying ++
                reverse ys
            =⟨ sym (append-[] (reverse ys)) ⟩ -- see append-[] lemma
                reverse ys ++ []
            =⟨⟩ -- unapplying reverse
                reverse ys ++ reverse []
            end
        reverse-distributivity (x :: xs) ys =
            begin
                reverse ((x :: xs) ++ ys)
            =⟨⟩ -- applying ++
                reverse (x :: (xs ++ ys))
            =⟨⟩ -- applying reverse
                reverse (xs ++ ys) ++ reverse [ x ]
            =⟨⟩ -- applying reverse
                reverse (xs ++ ys) ++ [ x ]
            =⟨ cong (_++ [ x ]) (reverse-distributivity xs ys) ⟩ -- using induction hypothesis
                (reverse ys ++ reverse xs) ++ [ x ]
            =⟨ append-assoc (reverse ys) (reverse xs) [ x ] ⟩ -- using associativity of ++
                reverse ys ++ (reverse xs ++ [ x ])
            =⟨⟩ -- unapplying inner ++
                reverse ys ++ (reverse (x :: xs))
            end

map-id : {A : Set} (xs : List A) → map id xs ≡ xs
map-id [] =
    begin
        map id []
    =⟨⟩ -- applying map
        []
    end
map-id (x :: xs) =
    begin
        map id (x :: xs)
    =⟨⟩ -- applying map
        id x :: map id xs
    =⟨⟩ -- applying id
        x :: map id xs
    =⟨ cong (x ::_) (map-id xs) ⟩ -- using induction hypothesis
        x :: xs
    end

_◦_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ◦ h = λ x → g (h x)

map-compose : {A B C : Set} (f : B → C) (g : A → B) (xs : List A)
    → map (f ◦ g) xs ≡ map f (map g xs)
map-compose f g [] =
    begin
        map (f ◦ g) []
    =⟨⟩ -- applying map
        []
    =⟨⟩ -- unapplying map
        map f []
    =⟨⟩ -- unapplying map
        map f (map g [])
    end
map-compose f g (x :: xs) =
    begin
        map (f ◦ g) (x :: xs)
    =⟨⟩ -- applying map
        (f ◦ g) x :: map (f ◦ g) xs
    =⟨⟩ -- applying function composition
        f (g x) :: map (f ◦ g) xs
    =⟨ cong (f (g x) ::_) (map-compose f g xs) ⟩ -- using induction hypothesis
        f (g x) :: map f (map g xs)
    =⟨⟩ -- unapplying map
        map f (g x :: map g xs)
    =⟨⟩ -- unapplying map
        map f (map g (x :: xs))
    end

map-length-invariant : {A B : Set} → (f : A → B) → (xs : List A) → length (map f xs) ≡ length xs
map-length-invariant f [] =
    begin
        length (map f [])
    end
map-length-invariant f (x :: xs) =
    begin
        length (map f (x :: xs))
    =⟨⟩
        length (f x :: map f xs)
    =⟨⟩
        1 + length (map f xs)
    =⟨ cong (1 +_) (map-length-invariant f xs) ⟩
        1 + length xs
    =⟨⟩
        length (x :: xs)
    end

reverse-acc : {A : Set} → List A → List A → List A
reverse-acc [] ys = ys
reverse-acc (x :: xs) ys = reverse-acc xs (x :: ys)

reverse’ : {A : Set} → List A → List A
reverse’ xs = reverse-acc xs []

reverse’-reverse : {A : Set} → (xs : List A) → reverse’ xs ≡ reverse xs
reverse’-reverse xs =
    begin
        reverse’ xs
    =⟨⟩ -- definition of reverse’
        reverse-acc xs []
    =⟨ reverse-acc-lemma xs [] ⟩ -- using reverse-acc-lemma
        reverse xs ++ []
    =⟨ append-[] (reverse xs) ⟩ -- using append-[]
        reverse xs
    end
    where
    reverse-acc-lemma : {A : Set} → (xs ys : List A)
        → reverse-acc xs ys ≡ reverse xs ++ ys
    reverse-acc-lemma [] ys =
        begin
            reverse-acc [] ys
        =⟨⟩ -- definition of reverse-acc
            ys
        =⟨⟩ -- unapplying ++
            [] ++ ys
        =⟨⟩ -- unapplying reverse
            reverse [] ++ ys
        end
    reverse-acc-lemma (x :: xs) ys =
        begin
            reverse-acc (x :: xs) ys
        =⟨⟩ -- definition of reverse-acc
            reverse-acc xs (x :: ys)
        =⟨ reverse-acc-lemma xs (x :: ys) ⟩ -- using induction hypothesis
            reverse xs ++ (x :: ys)
        =⟨⟩ -- unapplying ++
            reverse xs ++ ([ x ] ++ ys)
        =⟨ sym (append-assoc (reverse xs) [ x ] ys) ⟩ -- using associativity of append
            (reverse xs ++ [ x ]) ++ ys
        =⟨⟩ -- unapplying reverse
            reverse (x :: xs) ++ ys
        end

data Tree (A : Set) : Set where
    leaf : A → Tree A
    node : Tree A → Tree A → Tree A

flatten : {A : Set} → Tree A → List A
flatten (leaf x) = [ x ]
flatten (node t1 t2) = flatten t1 ++ flatten t2
flatten-acc : {A : Set} → Tree A → List A → List A
flatten-acc (leaf x) xs = x :: xs
flatten-acc (node t1 t2) xs =
    flatten-acc t1 (flatten-acc t2 xs)

flatten’ : {A : Set} → Tree A → List A
flatten’ t = flatten-acc t []

flatten-acc-flatten : {A : Set} (t : Tree A) (xs : List A) → flatten-acc t xs ≡ flatten t ++ xs
flatten-acc-flatten (leaf x) xs =
    begin
        flatten-acc (leaf x) xs
    =⟨⟩ -- definition of flatten-acc
        x :: xs
    =⟨⟩ -- unapplying ++
        [ x ] ++ xs
    =⟨⟩ -- unapplying flatten
        flatten (leaf x) ++ xs
    end
flatten-acc-flatten (node l r) xs =
    begin
        flatten-acc (node l r) xs
    =⟨⟩ -- applying flatten-acc
        flatten-acc l (flatten-acc r xs)
    =⟨ flatten-acc-flatten l (flatten-acc r xs) ⟩ -- using IH for l
        flatten l ++ (flatten-acc r xs)
    =⟨ cong (flatten l ++_) (flatten-acc-flatten r xs) ⟩ -- using IH for r
        flatten l ++ (flatten r ++ xs)
    =⟨ sym (append-assoc (flatten l) (flatten r) xs) ⟩ -- using append-assoc
        (flatten l ++ flatten r) ++ xs
    =⟨⟩ -- unapplying flatten
        (flatten (node l r)) ++ xs
    end
    
flatten’-flatten : {A : Set} → (t : Tree A) → flatten’ t ≡ flatten t
flatten’-flatten t = 
    begin
        flatten’ t
    =⟨⟩
        flatten-acc t []
    =⟨ flatten-acc-flatten t [] ⟩
        flatten t ++ []
    =⟨ append-[] (flatten t) ⟩
        flatten t
    end
 