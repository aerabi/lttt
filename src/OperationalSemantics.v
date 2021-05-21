Require Import Base.
Require Import SemanticsBase.

Inductive 𝔱sem : 𝔱 -> 𝔱 -> Prop :=
  | 𝔱sem_prj1 : forall t1 t2, 𝔱sem (𝔱prj 1 (𝔱pair t1 t2)) t1
  | 𝔱sem_prj2 : forall t1 t2, 𝔱sem (𝔱prj 2 (𝔱pair t1 t2)) t2
  | 𝔱sem_app : forall x t t', 𝔱sem (𝔱app (𝔱lambda x t) t') (𝔱subst t x t')
  | 𝔱sem_case1 : forall v x1 x2 t1 t2, 𝔱sem (𝔱case (𝔱inj 1 v) x1 t1 x2 t2) (𝔱subst t1 x1 v)
  | 𝔱sem_case2 : forall v x1 x2 t1 t2, 𝔱sem (𝔱case (𝔱inj 2 v) x1 t1 x2 t2) (𝔱subst t2 x2 v).

Inductive 𝔢sem : 𝔢 -> 𝔢 -> Prop :=
  | 𝔢sem_let_hole : forall e, 𝔢sem (𝔢holelet (𝔢hole) e) e
  | 𝔢sem_let : forall x1 x2 e1 e2 e, 𝔢sem (𝔢let x1 x2 (𝔢pair e1 e2) e) (𝔢subst (𝔢subst e x1 e1) x2 e2)
  | 𝔢sem_app : forall x e1 e2, 𝔢sem (𝔢app (𝔢lambda x e1) e2) (𝔢subst e1 x e2)
  | 𝔢sem_bind : forall x e1 e2, 𝔢sem (𝔢bind x (𝔢return e1) e2) (𝔢subst e2 x e1)
  | 𝔢sem_force_suspend : forall e, 𝔢sem (𝔢force (𝔱suspend e)) e
  | 𝔢sem_case1 : forall x1 x2 e1 e2 e, 𝔢sem (𝔢case (𝔢inj 1 e) x1 e1 x2 e2) (𝔢subst e1 x1 e)
  | 𝔢sem_case2 : forall x1 x2 e1 e2 e, 𝔢sem (𝔢case (𝔢inj 2 e) x1 e1 x2 e2) (𝔢subst e2 x2 e).


(*  | 𝔢sem_flor_let : forall v x e, 𝔢sem (𝔢florlet x (𝔢flor v) e) (𝔢subst e x v). *)