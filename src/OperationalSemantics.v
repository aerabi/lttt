Require Import Base.
Require Import SemanticsBase.

Inductive 𝔱sem : 𝔱 -> 𝔱 -> Prop :=
  | 𝔱sem_prj1 : forall t1 t2, 𝔱sem (𝔱prj 1 (𝔱pair t1 t2)) t1
  | 𝔱sem_prj2 : forall t1 t2, 𝔱sem (𝔱prj 2 (𝔱pair t1 t2)) t2
  | 𝔱sem_app : forall x t t', 𝔱sem (𝔱app (𝔱lambda x t) t') (𝔱subst t x t')
  | 𝔱sem_case1 : forall v x1 x2 t1 t2, 𝔱sem (𝔱case (𝔱inj 1 v) x1 t1 x2 t2) (𝔱subst t1 x1 v)
  | 𝔱sem_case2 : forall v x1 x2 t1 t2, 𝔱sem (𝔱case (𝔱inj 2 v) x1 t1 x2 t2) (𝔱subst t2 x2 v).