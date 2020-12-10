Require Import Base.
Require Import BaseProofs.

Inductive 𝔳 : Type :=
  | 𝔳hole : 𝔳
  | 𝔳pair : 𝔳 -> 𝔳 -> 𝔳
  | 𝔳inj : nat -> 𝔳 -> 𝔳
  | 𝔳lambda : 𝔵 -> 𝔳 -> 𝔳
  | 𝔳suspend : 𝔢 -> 𝔳
with 𝔫 : Type :=
  | 𝔫hole : 𝔫
  | 𝔫pair : 𝔢 -> 𝔢 -> 𝔫
  | 𝔫inj : nat -> 𝔢 -> 𝔫
  | 𝔫lambda : 𝔵 -> 𝔢 -> 𝔫
  | 𝔫return : 𝔢 -> 𝔫
  | 𝔫flor : 𝔳 -> 𝔫.

Fixpoint 𝔳2𝔱 (v : 𝔳) :=
  match v with
  | 𝔳hole => 𝔱hole
  | 𝔳pair v1 v2 => 𝔱pair (𝔳2𝔱 v1) (𝔳2𝔱 v2)
  | 𝔳inj z v1 => 𝔱inj z (𝔳2𝔱 v1)
  | 𝔳lambda x v1 => 𝔱lambda x (𝔳2𝔱 v1)
  | 𝔳suspend e => 𝔱suspend e
  end.

Definition 𝔫2𝔢 (n : 𝔫) :=
  match n with
  | 𝔫hole => 𝔢hole
  | 𝔫pair e1 e2 => 𝔢pair e1 e2
  | 𝔫inj z e => 𝔢inj z e
  | 𝔫lambda x e => 𝔢lambda x e
  | 𝔫return e => 𝔢return e
  | 𝔫flor v => 𝔢flor (𝔳2𝔱 v) 
  end.

Fixpoint 𝔱subst (t : 𝔱) (x : 𝔵) (v : 𝔳) : 𝔱 :=
  match t with
  | 𝔱id x' => (match var_eq x x' with true => 𝔳2𝔱 v | false => t end)
  | 𝔱hole => t
  | 𝔱holecase t' => 𝔱holecase (𝔱subst t' x v)
  | 𝔱pair t1 t2 => 𝔱pair (𝔱subst t1 x v) (𝔱subst t2 x v)
  | 𝔱prj z t' => 𝔱prj z (𝔱subst t' x v)
  | 𝔱inj z t' => 𝔱inj z (𝔱subst t' x v)
  | 𝔱case t' x1 t1 x2 t2 => 𝔱case (𝔱subst t' x v) x1 (𝔱subst t1 x v) x2 (𝔱subst t2 x v)
  | 𝔱lambda x' t' => 𝔱lambda x' (𝔱subst t' x v) 
  | 𝔱app t1 t2 => 𝔱app (𝔱subst t1 x v) (𝔱subst t2 x v)
  | 𝔱suspend e => t
  end.

Fixpoint 𝔢subst (e : 𝔢) (x : 𝔵) (n : 𝔢) : 𝔢 :=
  match e with
  | 𝔢id x' => (match var_eq x x' with true => n | false => e end)
  | 𝔢hole => e
  | 𝔢holecase e' => 𝔢holecase (𝔢subst e' x n)
  | 𝔢holelet e1 e2 => 𝔢holelet (𝔢subst e1 x n) (𝔢subst e2 x n)
  | 𝔢pair e1 e2 => 𝔢pair (𝔢subst e1 x n) (𝔢subst e2 x n)
  | 𝔢let x1 x2 e1 e2 => 𝔢let x1 x2 (𝔢subst e1 x n) (𝔢subst e2 x n)
  | 𝔢inj z e => 𝔢inj z (𝔢subst e x n)
  | 𝔢case e' x1 e1 x2 e2 => 𝔢case (𝔢subst e' x n) x1 (𝔢subst e1 x n) x2 (𝔢subst e2 x n)
  | 𝔢lambda x' e' => 𝔢lambda x' (𝔢subst e' x n) 
  | 𝔢app e1 e2 => 𝔢app (𝔢subst e1 x n) (𝔢subst e2 x n)
  | 𝔢return e' => 𝔢return (𝔢subst e' x n)
  | 𝔢bind x' e1 e2 => 𝔢bind x' (𝔢subst e1 x n) (𝔢subst e2 x n)
  | 𝔢force t => e
  | 𝔢flor t => e
  | 𝔢florlet x' e1 e2 => 𝔢florlet x' (𝔢subst e1 x n) (𝔢subst e2 x n)
  end.