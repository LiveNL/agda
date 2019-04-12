module Exam where

-- Base declarations --
infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x == x
{-# BUILTIN EQUALITY _==_  #-}

record Unit : Set where
{-# BUILTIN UNIT Unit #-}

data List (a : Set) : Set where
  [] : List a
  _::_ : a -> List a -> List a

-- Exercise setup --

-- types, either base type i, or a function type for types σ and τ.
data U : Set where
  i    : U
  _=>_ : U -> U -> U

-- a context, is a list of types.
Ctx = List U

-- we represent a variable of type s, by providing a 'proof' that s occurs in
-- the context Γ, given by data type s ∈ Γ.
data _∈_ (s : U) : Ctx -> Set where
  Top : ∀ { ctx }   -> s ∈ (s :: ctx)
  Pop : ∀ { ctx t } -> s ∈ ctx -> s ∈ (t :: ctx)

-- well-typed lambda terms, Term, with variables drawn from the context Γ.
data Term (Γ : Ctx) : U -> Set where
  var : ∀ {   τ } -> τ ∈ Γ             -> Term Γ τ
  app : ∀ { σ τ } -> Term Γ ( σ => τ ) -> Term Γ σ -> Term Γ τ
  lam : ∀ { σ τ } -> Term ( σ :: Γ ) τ -> Term Γ (σ => τ)

-- the careful choice of type indices, enables us to define a simple evaluator
-- that caries around an environment that contains values,
-- for all the free variables in the term.
Val : U -> Set
Val i        = Unit
Val (σ => τ) = Val σ -> Val τ

data Env : Ctx -> Set where
  Nil  : Env [] -- Env Nil?
  Cons : ∀ { u ctx } -> Val u -> Env ctx -> Env (u :: ctx)

-- Exercise a; Define the missing lookup
lookup : ∀ { s Γ } -> s ∈ Γ -> Env Γ -> Val s
lookup Top     (Cons x y)  = x
lookup (Pop x) (Cons y ys) = lookup x ys

eval : ∀ { Γ σ } -> Term Γ σ -> Env Γ -> Val σ
eval (app t1 t2) env = (eval t1 env) (eval t2 env)
eval (lam body) env  = λ x -> eval body (Cons x env)
eval (var j) env     = lookup j env

-- Exercise b; Define a data type for well-typed combinator terms:
--   - the atomic combinators S, K and I
--   - the application of one combinator to another
--   - variables drawn from some context
-- ! this term language should not include a constructor for lamdas.
-- ! choose your datatupe so that it can only represent well-typed SKI terms
-- HINT: You may want to use ghci to check the types of the three atomic
-- combinators for you

-- S f g x = (f x) (g x)
-- K y   x = y
-- I     x = x

-- s :: (t1 -> t2 -> t3) -> (t1 -> t2) -> t1 -> t3
-- k :: p1 -> p2 -> p1
-- i :: p -> p

data SKI : U -> Set where
  S      : ∀ { a b c } -> SKI (((((a => b) => c) => (a => b)) => a) => c)
  K      : ∀ { a b   } -> SKI ((a => b) => a)
  I      : ∀ { a     } -> SKI (a => a)
  SKIApp : ∀ { a b   } -> SKI (a => b) -> SKI a -> SKI b
  SKIVar : ∀ { a     } -> Val a -> SKI a

-- Other approach
-- data SKI : U -> Set where
--   S      : ∀ { a b c } -> SKI ((a => b) => c) -> SKI (a => b) -> SKI a -> SKI c
--   K      : ∀ { a b   } -> SKI a -> SKI b -> SKI a
--   I      : ∀ { a     } -> SKI a -> SKI a
--   SKIApp : ∀ { a b   } -> SKI (a => b) -> SKI a -> SKI b
--   SKIVar : ∀ { a     } -> Val a -> SKI a

const : {a b : Set} -> a -> b -> a
const = (λ x y -> x)

-- Exercise c; Define an interpretation function evalSKI
-- given an SKI term of type σ, and an env, produce value of type Val σ
-- evalSKI : ∀ { Γ σ } -> SKI σ -> Env Γ -> Val σ
-- evalSKI (S f g x)    e = {!!}
-- evalSKI (K y x)      e = evalSKI y e
-- evalSKI (I x)        e = evalSKI x e
-- evalSKI (SKIApp x y) e = {!   !}
-- evalSKI (SKIVar x)   e = {!   !}

evalSKI : ∀ { Γ σ } -> SKI σ -> Env Γ -> Val σ
evalSKI S            e = {! !}
evalSKI K            e = {! !}
evalSKI I            e = λ x → x -- id
evalSKI (SKIApp x y) e = {!  !}
evalSKI (SKIVar x)   e = x


lambda : ∀ {σ Γ τ} -> Term Γ σ -> SKI σ
lambda {s} {e} {t} (var x) with t == s
... | z = SKIApp K I
lambda {s} {e} {t} (app x y) = SKIApp (lambda x) (lambda y)
lambda {s} {e} {t} (lam x)   = SKIApp K K

-- Exercise d; Define a translation from lambda terms, Term Γ σ to your SKI
-- datatype. HINT: define an auxiliary function lamda to handle the case for
-- abstractions lam (what is its type?)
toSKI : ∀ { Γ σ } -> Term Γ σ -> SKI σ
toSKI {e} {s} (var x)   = SKIVar {!!}
toSKI {e} {s} (app x y) = SKIApp (toSKI x) (toSKI y)
toSKI {e} {s} (lam x)   = {! (lambda x) !}

-- Exercise e; formulate the property that the translation is correct, prove this for applications and variables
-- What goes wrong when you try to prove the branch for lamda abstractions?
-- What property can you formulate and prove that relates evalSKI and the auxiliary lambda function?

-- Well, I think we all can conclude that this is not possible with this state of the program.
